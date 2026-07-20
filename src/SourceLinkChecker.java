import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import com.sun.net.httpserver.HttpServer;

import com.jcraft.jsch.ChannelExec;
import com.jcraft.jsch.JSch;
import com.jcraft.jsch.Session;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.URLDecoder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * SourceLinkChecker - 원천사 연결 상태 점검 도구 (순수 Java 1.8, 단일 파일)
 *
 * 동작:
 *  1) 원천사 목록(id, name, endpoints[sendip/sendport/recvport])을 아래 우선순위로 로드
 *       (a) sourcesFile : 외부 JSON 파일에서 주입   <- FEP 등 DB 접속 불가 서버용
 *       (b) sources     : config.json 에 직접 내장
 *       (c) oracle.sourcesSql : Oracle DB 조회 (기존 방식)
 *  2) 사용자가 원천사 하나(또는 전체)를 선택
 *  3) 관리 대상 서버 N대에 SSH(비밀번호) 접속하여 ss/netstat 로
 *     "각 엔드포인트의 송신 IP:port ESTABLISHED / 수신 port LISTEN·ESTABLISHED" 존재 여부 판정
 *  4) 결과를 웹 UI 로 표시 (JDK 내장 HttpServer, 외부 웹프레임워크 의존성 없음)
 *
 * 이중화(다중 세션): 한 원천사가 서로 다른 IP:port 로 2개 이상의 송신 세션을 가질 수 있음.
 *   원천사에 endpoints 배열을 넣으면 엔드포인트별로 각각 점검한다.
 *
 * 의존성(런타임): DB 조회를 쓸 때만 lib/ 에 Oracle JDBC(ojdbc) jar 필요. SSH 는 JSch 필요.
 */
public class SourceLinkChecker {

    private static Map<String, Object> config;
    private static Map<String, Object> sshCfg;     // 전역 SSH 타임아웃
    private static Map<String, Object> envCfg;     // 운영/테스트 배너
    private static List<Object> businessesCfg;     // 업무(펌/가상)별 원천사출처 + servers
    private static File baseDir;
    private static File cfgFile;                    // config 파일 (재갱신 시 라이브 재조회용)

    // 원천사 정보 캐시 (biz별). 출처(파일/config/DB)는 최초 로드 또는 '재갱신' 시에만 접근. 내부 JSON 파일로 영속화.
    private static final Map<String, List<Src>> sourcesCache = new LinkedHashMap<String, List<Src>>();
    private static final Map<String, String> cacheUpdatedAt = new LinkedHashMap<String, String>();
    private static final Object CACHE_LOCK = new Object();
    private static File cacheFile;

    // 조회 이력 (최신순, 파일 영속화)
    private static final java.util.LinkedList<Map<String, Object>> history = new java.util.LinkedList<Map<String, Object>>();
    private static File historyFile;
    private static final int HISTORY_MAX = 200;
    // 원천사별 마지막 종합상태 (자동 점검 상태변화 알람용, key = biz/id)
    private static final Map<String, String> lastStatus = new java.util.concurrent.ConcurrentHashMap<String, String>();

    // =====================================================================
    // 데이터 모델
    // =====================================================================

    /** 원천사 엔드포인트(세션 정의) 1개. 이중화 시 원천사가 여러 개 가짐. */
    static class Ep {
        String label = "";
        String sendip = "", sendport = "", recvport = "";
        // 송신 점검 방식: session(ESTABLISHED 세션 확인, 연결유지형) / probe(능동 TCP 접속시도, 비연결유지) / skip(송신 제외)
        String checkMode = "session";
        // 예상 세션 개수(정상 기준). 0 = 미지정(송신은 ≥1, 수신은 LISTEN만). >0 이면 실제 세션수가 그 이상이어야 정상.
        int expectSend = 0, expectRecv = 0;
        boolean hasSend() { return !sendip.isEmpty() && !sendport.isEmpty(); }
        boolean hasRecv() { return !recvport.isEmpty(); }
        boolean isProbe() { return "probe".equals(checkMode); }
        boolean isSkip()  { return "skip".equals(checkMode); }
        // 송신을 실제로 판정하는가? (skip 이면 판정 안 함)
        boolean sendChecked() { return hasSend() && !isSkip(); }
    }

    /** DB sync/async 값(S/A 등) 또는 명시적 방식명 -> checkMode. A=async=session(연결유지), S=sync=skip(제외). */
    private static String toCheckMode(String v) {
        if (v == null) return "session";
        String t = v.trim().toUpperCase();
        if (t.equals("SESSION") || t.equals("PROBE") || t.equals("SKIP")) return t.toLowerCase();
        if (t.equals("A") || t.equals("ASYNC")) return "session";
        if (t.equals("S") || t.equals("SYNC")) return "skip";
        return "session";
    }

    /** 원천사 1개 (id, name, endpoints). */
    static class Src {
        String id = "", name = "";
        List<Ep> endpoints = new ArrayList<Ep>();
    }

    public static void main(String[] args) {
        String configPath = args.length > 0 ? args[0] : "config.json";
        cfgFile = new File(configPath).getAbsoluteFile();
        baseDir = cfgFile.getParentFile();

        // 1) config.json 읽기/파싱
        try {
            if (!cfgFile.isFile()) {
                fail("config.json 을 찾을 수 없습니다: " + cfgFile.getAbsolutePath()
                        + "\n     - run.bat 은 config.json 이 있는 폴더에서 실행하세요.");
                return;
            }
            String cfgText = new String(Files.readAllBytes(cfgFile.toPath()), StandardCharsets.UTF_8);
            config = asMap(Json.parse(cfgText));
        } catch (Exception e) {
            fail("config.json 파싱 실패 (JSON 문법 오류일 수 있음): " + rootMsg(e)
                    + "\n     - 마지막 항목 뒤 콤마(,), 값 안의 역슬래시(\\) 는 \\\\ 로, 따옴표는 \\\" 로 이스케이프했는지 확인하세요.");
            return;
        }
        sshCfg = asMap(config.get("ssh"));
        envCfg = asMap(config.get("env"));
        businessesCfg = asList(config.get("businesses"));
        if (businessesCfg.isEmpty()) {
            fail("config 에 businesses 가 없습니다. 업무(펌/가상)별 원천사출처(sourcesFile/sources/oracle)+servers 를 businesses 배열로 넣으세요.");
            return;
        }

        // 원천사 캐시 파일 로드 (config-prod.json -> config-prod.cache.json)
        String base = cfgFile.getName().replaceFirst("\\.json$", "");
        cacheFile = new File(baseDir, base + ".cache.json");
        loadCache();
        historyFile = new File(baseDir, base + ".history.json");
        loadHistory();

        // 2) Oracle 드라이버 등록 (DB 조회를 쓸 때만 필요 — 없어도 파일/config 주입은 정상 동작)
        try {
            Class.forName("oracle.jdbc.OracleDriver");
        } catch (Throwable e) {
            System.out.println("[INFO] oracle.jdbc.OracleDriver 미발견 - DB 조회를 쓰지 않으면 무시해도 됩니다 (파일/config 주입은 정상).");
        }

        // 3) 웹서버 기동
        int port = (int) num(asMap(config.get("web")).get("port"), 8095);
        try {
            HttpServer server = HttpServer.create(new InetSocketAddress(port), 0);
            server.createContext("/", new StaticHandler());
            server.createContext("/api/env", new EnvHandler());
            server.createContext("/api/history", new HistoryHandler());
            server.createContext("/api/businesses", new BusinessesHandler());
            server.createContext("/api/ssh", new SshHandler());
            server.createContext("/api/sources", new SourcesHandler());
            server.createContext("/api/check", new CheckHandler());
            server.createContext("/api/checkall", new CheckAllHandler());
            server.createContext("/api/config", new ConfigHandler());
            server.setExecutor(Executors.newFixedThreadPool(12));
            server.start();

            // 종료 시 열린 SSH 세션 정리
            Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
                public void run() {
                    for (Session s : sshPool.values()) { try { s.disconnect(); } catch (Exception ignore) {} }
                }
            }));
        } catch (java.net.BindException be) {
            fail("포트 " + port + " 를 열 수 없습니다 (이미 사용 중일 수 있음)."
                    + "\n     - config.json 의 web.port 를 다른 값으로 바꾸거나, 기존 프로세스를 종료하세요.");
            return;
        } catch (Exception e) {
            fail("웹서버 기동 실패: " + rootMsg(e));
            return;
        }

        String envName = str(envCfg.get("name"), "");
        String envTag = str(envCfg.get("tag"), "");
        System.out.println("======================================");
        System.out.println("  Source Link Checker" + (envName.isEmpty() ? "" : "  [ " + envName + " " + envTag + " ]"));
        System.out.println("  http://localhost:" + port + "  (Ctrl+C 종료)");
        System.out.println("  업무 " + businessesCfg.size() + "종 | config: " + cfgFile.getAbsolutePath());
        System.out.println("======================================");

        // 4) 서버 상시 주기 점검 스케줄러 (config.monitor.enabled=true 일 때)
        startMonitor();
    }

    private static void fail(String msg) {
        System.out.println();
        System.out.println("[ERROR] " + msg);
        System.out.println();
    }

    // ---------------------------------------------------------------------
    // HTTP Handlers
    // ---------------------------------------------------------------------

    /** 정적 파일: web/index.html */
    static class StaticHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            String path = ex.getRequestURI().getPath();
            if (path == null || path.equals("/")) path = "/index.html";
            if (path.contains("..")) { send(ex, 400, "text/plain", "bad path"); return; }

            // 항상 최신 페이지를 받도록 캐시 비활성(브라우저가 옛 index.html/js 붙잡는 문제 방지)
            ex.getResponseHeaders().set("Cache-Control", "no-cache, no-store, must-revalidate");
            File f = new File(new File(baseDir, "web"), path.substring(1));
            if (f.isFile()) {
                byte[] body = Files.readAllBytes(f.toPath());
                send(ex, 200, mime(path), body);
            } else {
                send(ex, 200, "text/html; charset=utf-8",
                        FALLBACK_HTML.getBytes(StandardCharsets.UTF_8));
            }
        }
    }

    /** GET /api/env -> { name, tag, color }  (운영/테스트 구분 배너용) */
    static class EnvHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            String json = "{\"name\":" + jstr(str(envCfg.get("name"), ""))
                    + ",\"tag\":" + jstr(str(envCfg.get("tag"), ""))
                    + ",\"color\":" + jstr(str(envCfg.get("color"), "")) + "}";
            sendJson(ex, 200, json);
        }
    }

    /** GET /api/history -> { entries:[{time,env,biz,bizName,mode,target,summary,status}...] } (최신순) */
    static class HistoryHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            sendJson(ex, 200, historyJson());
        }
    }

    /** GET /api/businesses -> { businesses:[{id,name,sourceType,sourceRef,dbUrl,dbUser}...] }  (탭 + 출처 표시용, 비밀번호 제외) */
    static class BusinessesHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            StringBuilder sb = new StringBuilder("{\"businesses\":[");
            for (int i = 0; i < businessesCfg.size(); i++) {
                Map<String, Object> b = asMap(businessesCfg.get(i));
                Map<String, Object> oracle = asMap(b.get("oracle"));
                if (i > 0) sb.append(',');
                sb.append("{\"id\":").append(jstr(str(b.get("id"), "")))
                  .append(",\"name\":").append(jstr(str(b.get("name"), str(b.get("id"), ""))))
                  .append(",\"sourceType\":").append(jstr(sourceType(b)))
                  .append(",\"sourceRef\":").append(jstr(sourceRef(b)))
                  .append(",\"dbUrl\":").append(jstr(str(oracle.get("url"), "")))
                  .append(",\"dbUser\":").append(jstr(str(oracle.get("user"), ""))).append('}');
            }
            sb.append("]}");
            sendJson(ex, 200, sb.toString());
        }
    }

    /**
     * GET /api/ssh?biz=firm&action=connect|status|disconnect
     *  - connect: 해당 업무 서버들에 SSH 접속(풀에 저장, 이후 재사용). 버튼으로만 호출.
     *  - disconnect: 세션 끊기.
     *  - status: 현재 접속 상태.
     *  응답: { servers:[{serverId,host,connected,error}...] }
     */
    static class SshHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            String q = ex.getRequestURI().getRawQuery();
            Map<String, Object> biz = bizById(param(q, "biz"));
            String action = str(param(q, "action"), "status");
            List<Object> servers = asList(biz.get("servers"));
            String[] errs = new String[servers.size()];
            for (int i = 0; i < errs.length; i++) errs[i] = "";

            if (action.equals("connect")) {
                ExecutorService pool = Executors.newFixedThreadPool(Math.max(1, servers.size()));
                List<Future<String>> fs = new ArrayList<Future<String>>();
                for (Object so : servers) {
                    final Map<String, Object> srv = asMap(so);
                    fs.add(pool.submit(new Callable<String>() {
                        public String call() { try { getSession(srv); return ""; } catch (Exception e) { return rootMsg(e); } }
                    }));
                }
                pool.shutdown();
                for (int i = 0; i < fs.size(); i++) {
                    try { errs[i] = str(fs.get(i).get(), ""); } catch (Exception e) { errs[i] = rootMsg(e); }
                }
            } else if (action.equals("disconnect")) {
                for (Object so : servers) dropSession(asMap(so));
            }

            StringBuilder sb = new StringBuilder("{\"servers\":[");
            for (int i = 0; i < servers.size(); i++) {
                Map<String, Object> srv = asMap(servers.get(i));
                if (i > 0) sb.append(',');
                sb.append("{\"serverId\":").append(jstr(str(srv.get("id"), "")))
                  .append(",\"host\":").append(jstr(str(srv.get("host"), "")))
                  .append(",\"connected\":").append(isConnected(srv))
                  .append(",\"error\":").append(jstr(errs[i])).append('}');
            }
            sb.append("]}");
            sendJson(ex, 200, sb.toString());
        }
    }

    /**
     * GET /api/sources?biz=firm[&refresh=1]
     *  - 캐시가 있으면 캐시 반환 (출처 접근 안 함).
     *  - 캐시가 없거나 refresh=1 이면 출처(파일/config/DB) 재조회 -> 캐시 갱신 + JSON 파일 저장.
     *  응답: { sources:[...], updatedAt:"...", origin:"file|config|db", fromDb:true/false, warn?:"..." }
     */
    static class SourcesHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            String q = ex.getRequestURI().getRawQuery();
            Map<String, Object> biz = bizById(param(q, "biz"));
            String bizId = str(biz.get("id"), "");
            boolean refresh = truthy(param(q, "refresh"));
            String origin = sourceType(biz);

            List<Src> list;
            String updatedAt;
            boolean fromDb = false;
            String warn = "";

            synchronized (CACHE_LOCK) {
                boolean cached = sourcesCache.containsKey(bizId) && !sourcesCache.get(bizId).isEmpty();
                if (refresh || !cached) {
                    try {
                        List<Src> fresh = resolveSources(biz);
                        sourcesCache.put(bizId, fresh);
                        cacheUpdatedAt.put(bizId, now());
                        saveCache();
                        fromDb = "db".equals(origin);
                    } catch (Exception e) {
                        if (!cached) { sendJson(ex, 500, "{\"error\":" + jstr("원천사 조회 실패: " + rootMsg(e)) + "}"); return; }
                        warn = "원천사 재조회 실패 - 이전 캐시를 표시합니다: " + rootMsg(e);  // 캐시 유지
                    }
                }
                list = sourcesCache.get(bizId);
                if (list == null) list = new ArrayList<Src>();
                updatedAt = str(cacheUpdatedAt.get(bizId), "");
            }

            StringBuilder sb = new StringBuilder("{\"sources\":[");
            for (int i = 0; i < list.size(); i++) {
                if (i > 0) sb.append(',');
                sb.append(sourceJson(list.get(i)));
            }
            sb.append("],\"updatedAt\":").append(jstr(updatedAt));
            sb.append(",\"origin\":").append(jstr(origin));
            sb.append(",\"fromDb\":").append(fromDb);
            if (!warn.isEmpty()) sb.append(",\"warn\":").append(jstr(warn));
            sb.append("}");
            sendJson(ex, 200, sb.toString());
        }
    }

    /** GET /api/check?biz=firm&id=XXX -> { source:{...}, results:[...] } */
    static class CheckHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            try {
                String q = ex.getRequestURI().getRawQuery();
                Map<String, Object> biz = bizById(param(q, "biz"));
                String bizId = str(biz.get("id"), "");
                String id = param(q, "id");
                if (id == null || id.isEmpty()) { sendJson(ex, 400, "{\"error\":\"id 파라미터 필요\"}"); return; }

                // 캐시에서 원천사 조회 (출처 접근은 /api/sources 재갱신에서만)
                final Src src = findInCache(bizId, id);
                if (src == null) {
                    sendJson(ex, 400, "{\"error\":" + jstr("원천사 정보가 캐시에 없습니다. 상단 '재갱신'으로 먼저 불러오세요. (id=" + id + ")") + "}");
                    return;
                }

                List<Object> servers = asList(biz.get("servers"));
                // 서버별 SSH 점검을 병렬 실행
                ExecutorService pool = Executors.newFixedThreadPool(Math.max(1, servers.size()));
                List<Future<CheckResult>> futures = new ArrayList<Future<CheckResult>>();
                for (Object so : servers) {
                    final Map<String, Object> srv = asMap(so);
                    futures.add(pool.submit(new Callable<CheckResult>() {
                        public CheckResult call() { return sshCheck(srv, src); }
                    }));
                }
                pool.shutdown();

                List<CheckResult> results = new ArrayList<CheckResult>();
                StringBuilder sb = new StringBuilder();
                sb.append("{\"source\":").append(sourceJson(src)).append(",\"results\":[");
                for (int i = 0; i < futures.size(); i++) {
                    CheckResult r;
                    try { r = futures.get(i).get(); }
                    catch (Exception e) { r = new CheckResult(); r.error = rootMsg(e); }
                    results.add(r);
                    if (i > 0) sb.append(',');
                    sb.append(r.toJson());
                }
                // 클러스터(서버 전체) 합산 종합상태
                SrcStat stat = computeSrcStat(results);
                sb.append("],\"status\":").append(jstr(stat.status))
                  .append(",\"sendState\":").append(jstr(stat.sendState))
                  .append(",\"recvState\":").append(jstr(stat.recvState))
                  .append(",\"sendTotal\":").append(stat.sendTotal)
                  .append(",\"sendNeed\":").append(stat.sendNeed)
                  .append(",\"recvTotal\":").append(stat.recvTotal)
                  .append(",\"recvNeed\":").append(stat.recvNeed).append("}");
                sendJson(ex, 200, sb.toString());

                // 이력 기록
                Map<String, Object> h = new LinkedHashMap<String, Object>();
                h.put("time", now());
                h.put("env", str(envCfg.get("tag"), ""));
                h.put("biz", bizId);
                h.put("bizName", str(biz.get("name"), bizId));
                h.put("mode", "single");
                h.put("target", src.name.isEmpty() ? id : src.name);
                h.put("summary", statSummary(stat));
                String st1 = stat.status;
                h.put("status", st1);
                recordHistory(h);
                lastStatus.put(bizId + "/" + id, st1);   // 자동 점검 알람 기준 갱신
            } catch (Exception e) {
                sendJson(ex, 500, "{\"error\":" + jstr(rootMsg(e)) + "}");
            }
        }
    }

    /**
     * GET /api/checkall?biz=firm[&ids=a,b,c]  (전체/선택 조회)
     * 서버당 ss 를 1회만 실행하고, 그 출력으로 선택된 모든 원천사(및 모든 엔드포인트)를 판정 (효율적).
     * 응답: { servers:[{serverId,host}], results:[{id,name,...,sendCnt,listenCnt,sessSum,errCnt,servers:[...]}] }
     */
    static class CheckAllHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            try {
                String q = ex.getRequestURI().getRawQuery();
                Map<String, Object> biz = bizById(param(q, "biz"));
                String bizId = str(biz.get("id"), "");
                String idsParam = param(q, "ids");
                boolean auto = truthy(param(q, "auto"));   // 자동 점검이면 요약 이력은 남기지 않음(알람만)

                List<Src> all;
                synchronized (CACHE_LOCK) {
                    List<Src> c = sourcesCache.get(bizId);
                    all = (c == null) ? new ArrayList<Src>() : new ArrayList<Src>(c);
                }
                if (all.isEmpty()) { sendJson(ex, 400, "{\"error\":\"원천사 캐시가 없습니다. 재갱신으로 먼저 불러오세요.\"}"); return; }

                List<Src> sources = new ArrayList<Src>();
                if (idsParam == null || idsParam.isEmpty()) {
                    sources = all;
                } else {
                    java.util.Set<String> want = new java.util.HashSet<String>(java.util.Arrays.asList(idsParam.split(",")));
                    for (Src s : all) if (want.contains(s.id)) sources.add(s);
                }
                if (sources.isEmpty()) { sendJson(ex, 400, "{\"error\":\"선택된 원천사가 없습니다.\"}"); return; }

                BulkResult br = performBulk(biz, sources, auto);
                sendJson(ex, 200, bulkJson(br));
            } catch (Exception e) {
                sendJson(ex, 500, "{\"error\":" + jstr(rootMsg(e)) + "}");
            }
        }
    }

    // ---------------------------------------------------------------------
    // 전체 점검 공통 로직 (HTTP 전체조회 + 서버 상시 스케줄러 공용)
    // ---------------------------------------------------------------------

    /** 서버 1대에 대한 원천사별 점검 결과 묶음. */
    static class SrcResult {
        Src src;
        int sendCnt = 0, listenCnt = 0, sessSum = 0, errCnt = 0;
        String status = "mut";
        SrcStat stat = new SrcStat();   // 클러스터 합산 통계(실제/기대)
        List<CheckResult> perServer = new ArrayList<CheckResult>();
    }

    /** 전체 점검 1회 결과. */
    static class BulkResult {
        int M = 0;
        List<Map<String, Object>> serverMeta = new ArrayList<Map<String, Object>>();
        List<SrcResult> results = new ArrayList<SrcResult>();
        int okSrc = 0, warnSrc = 0, badSrc = 0;
    }

    /**
     * 선택된 원천사 전체를 서버당 ss 1회로 판정한다.
     * auto=true 이면 상태변화 시 이력('alarm') + 알람 파일 기록, auto=false 이면 요약 이력만 기록.
     * HTTP 전체조회 핸들러와 서버 상시 스케줄러가 함께 사용한다.
     */
    private static BulkResult performBulk(Map<String, Object> biz, List<Src> sources, boolean auto) {
        String bizId = str(biz.get("id"), "");
        String bizName = str(biz.get("name"), bizId);

        // 선택 원천사 전체(모든 엔드포인트)의 관련 라인만 걸러오는 union grep + probe 대상 합집합
        StringBuilder rx = new StringBuilder();
        LinkedHashMap<String, String> probeSet = new LinkedHashMap<String, String>();   // ip:port 중복 제거
        for (Src s : sources) {
            String one = srcRx(s);
            if (!one.isEmpty()) { if (rx.length() > 0) rx.append("|"); rx.append(one); }
            for (String p : srcProbes(s)) probeSet.put(p, p);
        }
        final String cmd = buildCmd(rx.toString(), new ArrayList<String>(probeSet.keySet()));
        final int execTimeout = (int) num(sshCfg.get("execTimeoutSec"), 10) * 1000;

        // 서버당 1회만 실행 (병렬)
        final List<Object> servers = asList(biz.get("servers"));
        final int M = servers.size();
        ExecutorService pool = Executors.newFixedThreadPool(Math.max(1, M));
        List<Future<String[]>> fs = new ArrayList<Future<String[]>>();
        for (Object so : servers) {
            final Map<String, Object> srv = asMap(so);
            fs.add(pool.submit(new Callable<String[]>() {
                public String[] call() {
                    try { return new String[]{ execViaPool(srv, cmd, execTimeout), "" }; }
                    catch (Exception e) { return new String[]{ "", rootMsg(e) }; }
                }
            }));
        }
        pool.shutdown();
        String[] outs = new String[M];
        String[] errs = new String[M];
        for (int i = 0; i < M; i++) {
            try { String[] rr = fs.get(i).get(); outs[i] = rr[0]; errs[i] = rr[1]; }
            catch (Exception e) { outs[i] = ""; errs[i] = rootMsg(e); }
        }

        BulkResult br = new BulkResult();
        br.M = M;
        for (int i = 0; i < M; i++) {
            Map<String, Object> srv = asMap(servers.get(i));
            Map<String, Object> meta = new LinkedHashMap<String, Object>();
            meta.put("serverId", str(srv.get("id"), ""));
            meta.put("host", str(srv.get("host"), ""));
            br.serverMeta.add(meta);
        }

        for (Src s : sources) {
            SrcResult sr = new SrcResult();
            sr.src = s;
            for (int i = 0; i < M; i++) {
                Map<String, Object> srv = asMap(servers.get(i));
                CheckResult r = new CheckResult();
                r.serverId = str(srv.get("id"), "");
                r.host = str(srv.get("host"), "");
                if (errs[i] != null && !errs[i].isEmpty()) { r.ok = false; r.error = errs[i]; sr.errCnt++; }
                else {
                    fillEndpoints(r, s, outs[i]);
                    r.ok = true;
                    if (r.sendConnected) sr.sendCnt++;
                    if (r.recvListening) sr.listenCnt++;
                    sr.sessSum += r.recvEstabCount;
                }
                sr.perServer.add(r);
            }
            // 클러스터(서버 전체) 합산 종합상태
            SrcStat stat = computeSrcStat(sr.perServer);
            sr.status = stat.status;
            sr.stat = stat;
            if (sr.status.equals("ok")) br.okSrc++; else if (sr.status.equals("bad")) br.badSrc++; else br.warnSrc++;

            // 상태변화 알람 (auto 일 때만): 이력 + 알람 파일
            String skey = bizId + "/" + s.id;
            String prev = lastStatus.get(skey);
            if (auto && prev != null && !prev.equals(sr.status)) {
                String summary = statSummary(stat);
                Map<String, Object> al = new LinkedHashMap<String, Object>();
                al.put("time", now());
                al.put("env", str(envCfg.get("tag"), ""));
                al.put("biz", bizId);
                al.put("bizName", bizName);
                al.put("mode", "alarm");
                al.put("target", s.name.isEmpty() ? s.id : s.name);
                al.put("summary", statusKo(prev) + " → " + statusKo(sr.status) + " (" + summary + ")");
                al.put("status", sr.status);
                recordHistory(al);
                writeAlarmFile(bizId, bizName, s, prev, sr.status, summary);
            }
            lastStatus.put(skey, sr.status);
            br.results.add(sr);
        }

        // 수동 조회만 요약 이력 기록 (자동 점검은 상태변화 알람만 남김)
        if (!auto) {
            Map<String, Object> h = new LinkedHashMap<String, Object>();
            h.put("time", now());
            h.put("env", str(envCfg.get("tag"), ""));
            h.put("biz", bizId);
            h.put("bizName", bizName);
            h.put("mode", "bulk");
            h.put("target", sources.size() + "건");
            h.put("summary", "정상 " + br.okSrc + " · 주의 " + br.warnSrc + " · 장애 " + br.badSrc + " (서버 " + M + "대)");
            h.put("status", br.badSrc > 0 ? "bad" : (br.warnSrc > 0 ? "warn" : "ok"));
            recordHistory(h);
        }
        return br;
    }

    /** BulkResult -> /api/checkall 응답 JSON (프론트 계약 유지). */
    private static String bulkJson(BulkResult br) {
        StringBuilder sb = new StringBuilder("{\"servers\":[");
        for (int i = 0; i < br.serverMeta.size(); i++) {
            Map<String, Object> m = br.serverMeta.get(i);
            if (i > 0) sb.append(',');
            sb.append("{\"serverId\":").append(jstr(str(m.get("serverId"), "")))
              .append(",\"host\":").append(jstr(str(m.get("host"), ""))).append('}');
        }
        sb.append("],\"results\":[");
        for (int si = 0; si < br.results.size(); si++) {
            SrcResult sr = br.results.get(si);
            Src s = sr.src;
            if (si > 0) sb.append(',');
            StringBuilder per = new StringBuilder("[");
            for (int i = 0; i < sr.perServer.size(); i++) {
                CheckResult r = sr.perServer.get(i);
                if (i > 0) per.append(',');
                per.append("{\"serverId\":").append(jstr(r.serverId))
                   .append(",\"ok\":").append(r.ok)
                   .append(",\"sendConnected\":").append(r.sendConnected)
                   .append(",\"sendCount\":").append(r.sendCount)
                   .append(",\"recvListening\":").append(r.recvListening)
                   .append(",\"recvEstabCount\":").append(r.recvEstabCount)
                   .append(",\"error\":").append(jstr(r.error)).append('}');
            }
            per.append("]");
            List<Ep> sList = sendsOf(s), rList = recvsOf(s);
            Ep fs = sList.isEmpty() ? new Ep() : sList.get(0);
            Ep fr = rList.isEmpty() ? new Ep() : rList.get(0);
            sb.append("{\"id\":").append(jstr(s.id))
              .append(",\"name\":").append(jstr(s.name))
              .append(",\"sendip\":").append(jstr(fs.sendip))
              .append(",\"sendport\":").append(jstr(fs.sendport))
              .append(",\"recvport\":").append(jstr(fr.recvport))
              .append(",\"sendCount2\":").append(sList.size())
              .append(",\"recvCount2\":").append(rList.size())
              .append(",\"sendApp\":").append(srcSendApplicable(s))
              .append(",\"recvApp\":").append(srcRecvApplicable(s))
              .append(",\"sendCnt\":").append(sr.sendCnt)
              .append(",\"listenCnt\":").append(sr.listenCnt)
              .append(",\"sessSum\":").append(sr.sessSum)
              .append(",\"errCnt\":").append(sr.errCnt)
              .append(",\"status\":").append(jstr(sr.status))
              .append(",\"sendState\":").append(jstr(sr.stat.sendState))
              .append(",\"recvState\":").append(jstr(sr.stat.recvState))
              .append(",\"sendTotal\":").append(sr.stat.sendTotal)
              .append(",\"sendNeed\":").append(sr.stat.sendNeed)
              .append(",\"recvTotal\":").append(sr.stat.recvTotal)
              .append(",\"recvNeed\":").append(sr.stat.recvNeed)
              .append(",\"servers\":").append(per).append('}');
        }
        return sb.append("]}").toString();
    }

    // ---------------------------------------------------------------------
    // 서버 상시 스케줄러 (브라우저 없이도 주기 점검 + 상태변화 알람 파일)
    // ---------------------------------------------------------------------

    /** config.monitor.alarmDir 로 지정된 알람 출력 디렉토리 (미지정 시 baseDir/alarms). */
    private static File alarmDir() {
        Map<String, Object> mon = asMap(config.get("monitor"));
        String d = str(mon.get("alarmDir"), "").trim();
        if (d.isEmpty()) d = "alarms";
        File f = new File(d);
        if (!f.isAbsolute()) f = new File(baseDir, d);
        return f;
    }

    /** 상태변화를 알람 로그 파일에 한 줄 append. 파일: {alarmDir}/alarm-YYYYMMDD.log */
    private static void writeAlarmFile(String bizId, String bizName, Src s, String prev, String st, String summary) {
        try {
            File dir = alarmDir();
            if (!dir.isDirectory() && !dir.mkdirs()) {
                System.out.println("[alarm] 디렉토리 생성 실패: " + dir.getAbsolutePath());
                return;
            }
            String day = new java.text.SimpleDateFormat("yyyyMMdd").format(new java.util.Date());
            File f = new File(dir, "alarm-" + day + ".log");
            // 포맷: 시각 | 환경 | biz/id | 원천사명 | 이전 -> 현재 | 요약   (탭 아님, 파이프 구분)
            String line = now() + " | " + str(envCfg.get("tag"), "-")
                    + " | " + bizId + "/" + s.id
                    + " | " + (s.name.isEmpty() ? s.id : s.name)
                    + " | " + statusKo(prev) + " -> " + statusKo(st)
                    + " | " + summary + System.lineSeparator();
            Files.write(f.toPath(), line.getBytes(StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.CREATE, java.nio.file.StandardOpenOption.APPEND);
        } catch (Exception e) {
            System.out.println("[alarm] 파일 기록 실패: " + rootMsg(e));
        }
    }

    private static java.util.concurrent.ScheduledExecutorService monitorSch;   // 실행 중인 스케줄러 (설정 변경 시 재기동)

    /** config.monitor.enabled=true 이면 주기 스케줄러 기동. 이미 돌고 있으면 중지 후 재기동(설정 라이브 반영). */
    private static synchronized void startMonitor() {
        if (monitorSch != null) { monitorSch.shutdownNow(); monitorSch = null; }
        Map<String, Object> mon = asMap(config.get("monitor"));
        if (!Boolean.TRUE.equals(mon.get("enabled"))) {
            System.out.println("[monitor] 비활성 — config.monitor.enabled=true 로 서버 상시 점검을 켤 수 있습니다.");
            return;
        }
        final int interval = Math.max(5, (int) num(mon.get("intervalSec"), 60));
        final List<Object> bizFilter = asList(mon.get("businesses"));   // 비어있으면 전체 업무
        java.util.concurrent.ScheduledExecutorService sch = Executors.newScheduledThreadPool(1);
        sch.scheduleWithFixedDelay(new Runnable() {
            public void run() {
                try { monitorTick(bizFilter); }
                catch (Throwable t) { System.out.println("[monitor] tick 오류: " + rootMsg(t)); }
            }
        }, interval, interval, java.util.concurrent.TimeUnit.SECONDS);
        monitorSch = sch;
        System.out.println("[monitor] 서버 상시 점검 ON — 주기 " + interval + "초, 알람 파일 디렉토리: " + alarmDir().getAbsolutePath());
    }

    /** 스케줄러 1회 실행: 대상 업무별로 원천사 전체를 자동 점검(상태변화 시 알람 파일). */
    private static void monitorTick(List<Object> bizFilter) {
        java.util.Set<String> want = new java.util.HashSet<String>();
        for (Object o : bizFilter) want.add(String.valueOf(o));
        for (Object o : businessesCfg) {
            Map<String, Object> biz = asMap(o);
            String bizId = str(biz.get("id"), "");
            if (!want.isEmpty() && !want.contains(bizId)) continue;
            List<Src> sources = monitorSources(bizId, biz);
            if (sources.isEmpty()) continue;
            try { performBulk(biz, sources, true); }
            catch (Exception e) { System.out.println("[monitor] " + bizId + " 점검 오류: " + rootMsg(e)); }
        }
    }

    /** 스케줄러용 원천사 확보: 캐시에 있으면 사용, 없으면 출처에서 로드해 캐시에 채운다(브라우저 없이도 동작). */
    private static List<Src> monitorSources(String bizId, Map<String, Object> biz) {
        synchronized (CACHE_LOCK) {
            List<Src> c = sourcesCache.get(bizId);
            if (c != null && !c.isEmpty()) return new ArrayList<Src>(c);
        }
        try {
            List<Src> fresh = resolveSources(biz);
            synchronized (CACHE_LOCK) {
                sourcesCache.put(bizId, fresh);
                cacheUpdatedAt.put(bizId, now());
                saveCache();
            }
            return fresh;
        } catch (Exception e) {
            System.out.println("[monitor] " + bizId + " 원천사 로드 실패(스킵): " + rootMsg(e));
            return new ArrayList<Src>();
        }
    }

    // ---------------------------------------------------------------------
    // 설정 편집 (설정 탭): 원천사 목록 / 서버 / monitor 를 웹에서 저장
    // ---------------------------------------------------------------------

    private static final Object CONFIG_LOCK = new Object();

    /**
     * GET  /api/config           -> 편집용 설정 payload (원천사/서버/monitor)
     * POST /api/config           -> { section:"sources|servers|monitor", biz?, sources?/servers?/monitor? } 저장
     */
    static class ConfigHandler implements HttpHandler {
        public void handle(HttpExchange ex) throws IOException {
            try {
                if ("POST".equalsIgnoreCase(ex.getRequestMethod())) { handleSave(ex); return; }
                sendJson(ex, 200, configJson());
            } catch (Exception e) {
                sendJson(ex, 500, "{\"error\":" + jstr(rootMsg(e)) + "}");
            }
        }
    }

    /** 편집용 설정 payload. 서버 비밀번호도 포함(내부 localhost 관리도구, config 에 이미 평문). */
    private static String configJson() {
        Map<String, Object> mon = asMap(config.get("monitor"));
        StringBuilder sb = new StringBuilder("{");
        sb.append("\"configPath\":").append(jstr(cfgFile.getAbsolutePath()));
        // monitor
        sb.append(",\"monitor\":{")
          .append("\"enabled\":").append(Boolean.TRUE.equals(mon.get("enabled")))
          .append(",\"intervalSec\":").append((int) num(mon.get("intervalSec"), 60))
          .append(",\"alarmDir\":").append(jstr(str(mon.get("alarmDir"), "alarms")))
          .append(",\"alarmDirResolved\":").append(jstr(alarmDir().getAbsolutePath()))
          .append(",\"businesses\":[");
        List<Object> mb = asList(mon.get("businesses"));
        for (int i = 0; i < mb.size(); i++) { if (i > 0) sb.append(','); sb.append(jstr(String.valueOf(mb.get(i)))); }
        sb.append("]}");
        // businesses
        sb.append(",\"businesses\":[");
        for (int bi = 0; bi < businessesCfg.size(); bi++) {
            Map<String, Object> biz = asMap(businessesCfg.get(bi));
            String bizId = str(biz.get("id"), "");
            String origin = sourceType(biz);
            Map<String, Object> oracle = asMap(biz.get("oracle"));
            if (bi > 0) sb.append(',');
            sb.append("{\"id\":").append(jstr(bizId))
              .append(",\"name\":").append(jstr(str(biz.get("name"), bizId)))
              .append(",\"sourceType\":").append(jstr(origin))
              .append(",\"sourceMode\":").append(jstr(str(biz.get("sourceMode"), "")))
              .append(",\"sourceRef\":").append(jstr(sourceRef(biz)))
              .append(",\"sourcesFile\":").append(jstr(str(biz.get("sourcesFile"), "")))
              .append(",\"hasFile\":").append(!str(biz.get("sourcesFile"), "").trim().isEmpty())
              .append(",\"hasConfig\":").append(biz.get("sources") != null)
              .append(",\"hasDb\":").append(!str(oracle.get("sourcesSql"), "").trim().isEmpty())
              .append(",\"oracle\":{")
                .append("\"url\":").append(jstr(str(oracle.get("url"), "")))
                .append(",\"user\":").append(jstr(str(oracle.get("user"), "")))
                .append(",\"password\":").append(jstr(str(oracle.get("password"), "")))
                .append(",\"sourcesSql\":").append(jstr(str(oracle.get("sourcesSql"), ""))).append("}")
              .append(",\"editableSources\":").append(!origin.equals("db"));
            // servers
            sb.append(",\"servers\":[");
            List<Object> servers = asList(biz.get("servers"));
            for (int i = 0; i < servers.size(); i++) {
                Map<String, Object> sv = asMap(servers.get(i));
                if (i > 0) sb.append(',');
                sb.append("{\"id\":").append(jstr(str(sv.get("id"), "")))
                  .append(",\"host\":").append(jstr(str(sv.get("host"), "")))
                  .append(",\"sshPort\":").append((int) num(sv.get("sshPort"), 22))
                  .append(",\"user\":").append(jstr(str(sv.get("user"), "")))
                  .append(",\"password\":").append(jstr(str(sv.get("password"), ""))).append('}');
            }
            sb.append("]");
            // sources (편집용: 파일/config 는 현재값 로드, DB 는 캐시)
            List<Src> list;
            if (origin.equals("db")) {
                synchronized (CACHE_LOCK) { List<Src> c = sourcesCache.get(bizId); list = (c == null) ? new ArrayList<Src>() : new ArrayList<Src>(c); }
            } else {
                try { list = resolveSources(biz); }
                catch (Exception e) { synchronized (CACHE_LOCK) { List<Src> c = sourcesCache.get(bizId); list = (c == null) ? new ArrayList<Src>() : new ArrayList<Src>(c); } }
            }
            sb.append(",\"sources\":[");
            for (int i = 0; i < list.size(); i++) { if (i > 0) sb.append(','); sb.append(sourceJson(list.get(i))); }
            sb.append("]}");
        }
        sb.append("]}");
        return sb.toString();
    }

    private static void handleSave(HttpExchange ex) throws IOException {
        String body = readBody(ex);
        Map<String, Object> req;
        try { req = asMap(Json.parse(body)); }
        catch (Exception e) { sendJson(ex, 400, "{\"error\":" + jstr("요청 JSON 파싱 실패: " + rootMsg(e)) + "}"); return; }
        String section = str(req.get("section"), "");

        try {
            synchronized (CONFIG_LOCK) {
                if (section.equals("monitor")) {
                    Map<String, Object> mon = asMap(req.get("monitor"));
                    config.put("monitor", mon);
                    saveConfigFile();
                    startMonitor();   // 스케줄러 라이브 재기동
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("주기 점검 설정 저장 및 재기동 완료.") + "}");
                    return;
                }

                String bizId = str(req.get("biz"), "");
                Map<String, Object> biz = null;
                for (Object o : businessesCfg) { Map<String, Object> b = asMap(o); if (bizId.equals(str(b.get("id"), ""))) { biz = b; break; } }
                if (biz == null) { sendJson(ex, 400, "{\"error\":" + jstr("업무를 찾을 수 없습니다: " + bizId) + "}"); return; }

                if (section.equals("origin")) {
                    // 원천사 방식 전환: file/config/db. DB 정보 등 다른 데이터는 지우지 않고 sourceMode 만 고정.
                    String mode = str(req.get("mode"), "").trim();
                    if (!mode.equals("file") && !mode.equals("config") && !mode.equals("db"))
                        { sendJson(ex, 400, "{\"error\":\"mode 는 file|config|db 여야 합니다.\"}"); return; }
                    if (mode.equals("file") && str(biz.get("sourcesFile"), "").trim().isEmpty())
                        biz.put("sourcesFile", "sources-" + bizId + ".json");   // 파일 방식인데 경로 없으면 기본 파일명 지정
                    if (mode.equals("config") && biz.get("sources") == null)
                        biz.put("sources", new ArrayList<Object>());             // 설정 방식인데 목록 없으면 빈 목록
                    biz.put("sourceMode", mode);
                    saveConfigFile();
                    // 캐시 재적재(가능하면). 실패해도 방식 전환 자체는 성공 처리.
                    String warn = "";
                    try {
                        List<Src> fresh = resolveSources(biz);
                        synchronized (CACHE_LOCK) { sourcesCache.put(bizId, fresh); cacheUpdatedAt.put(bizId, now()); saveCache(); }
                    } catch (Exception re) { warn = " (원천사 로드 경고: " + rootMsg(re) + ")"; }
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("원천사 방식을 '" + mode + "' 로 전환했습니다." + warn) + "}");
                    return;
                }

                if (section.equals("oracle")) {
                    // DB 접속정보 저장 (방식 전환과 무관 — 저장만; 지금 방식이 file/config 면 저장돼 있어도 사용 안 함).
                    Map<String, Object> oracle = asMap(req.get("oracle"));
                    Map<String, Object> o = new LinkedHashMap<String, Object>();
                    o.put("url", str(oracle.get("url"), ""));
                    o.put("user", str(oracle.get("user"), ""));
                    o.put("password", str(oracle.get("password"), ""));
                    o.put("sourcesSql", str(oracle.get("sourcesSql"), ""));
                    biz.put("oracle", o);
                    saveConfigFile();
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("DB 접속정보 저장 완료.") + "}");
                    return;
                }

                if (section.equals("exportDb")) {
                    // 로컬에서 DB 를 조회해 그 결과를 파일로 내보내고 파일 방식으로 전환.
                    // 이후 사용자가 DB 에 없는 원천사를 파일(설정 탭)에서 추가로 편집한다.
                    Map<String, Object> oracle = asMap(biz.get("oracle"));
                    if (str(oracle.get("sourcesSql"), "").trim().isEmpty())
                        { sendJson(ex, 400, "{\"error\":\"DB 접속정보(sourcesSql)가 없습니다. 먼저 'DB 정보 저장'을 하세요.\"}"); return; }
                    List<Src> list;
                    try { list = querySources(oracle); }
                    catch (Exception qe) { sendJson(ex, 500, "{\"error\":" + jstr("DB 조회 실패: " + rootMsg(qe)) + "}"); return; }

                    String file = str(req.get("file"), "").trim();
                    if (file.isEmpty()) file = str(biz.get("sourcesFile"), "").trim();
                    if (file.isEmpty()) file = "sources-" + bizId + ".json";
                    File f = new File(file);
                    if (!f.isAbsolute()) f = new File(baseDir, file);
                    Files.write(f.toPath(), sourcesFileJson(list).getBytes(StandardCharsets.UTF_8));

                    // 파일 방식으로 전환 + 경로 지정 (DB 정보는 그대로 보존)
                    biz.put("sourcesFile", file);
                    biz.put("sourceMode", "file");
                    saveConfigFile();
                    synchronized (CACHE_LOCK) { sourcesCache.put(bizId, list); cacheUpdatedAt.put(bizId, now()); saveCache(); }
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("DB에서 " + list.size() + "건을 조회해 " + f.getName()
                            + " 로 저장하고 '파일 주입' 방식으로 전환했습니다. 이제 원천사 목록에서 DB에 없는 항목을 추가·저장하면 이 파일에 반영됩니다.") + "}");
                    return;
                }

                if (section.equals("servers")) {
                    List<Object> servers = asList(req.get("servers"));
                    // 최소 검증
                    for (Object o : servers) { Map<String, Object> sv = asMap(o);
                        if (str(sv.get("id"), "").trim().isEmpty() || str(sv.get("host"), "").trim().isEmpty())
                            { sendJson(ex, 400, "{\"error\":\"서버는 id 와 host 가 필요합니다.\"}"); return; } }
                    biz.put("servers", servers);
                    saveConfigFile();
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("서버 목록 저장 완료.") + "}");
                    return;
                }

                if (section.equals("sources")) {
                    String origin = sourceType(biz);
                    if (origin.equals("db")) { sendJson(ex, 400, "{\"error\":\"DB 방식 원천사는 편집할 수 없습니다. sourcesFile/sources 방식으로 전환하세요.\"}"); return; }
                    List<Src> list = parseSourcesList(asList(req.get("sources")));
                    for (Src s : list) if (s.id.isEmpty()) { sendJson(ex, 400, "{\"error\":\"원천사는 id 가 필요합니다.\"}"); return; }

                    if (origin.equals("file")) {
                        String file = str(biz.get("sourcesFile"), "").trim();
                        File f = new File(file); if (!f.isAbsolute()) f = new File(baseDir, file);
                        Files.write(f.toPath(), sourcesFileJson(list).getBytes(StandardCharsets.UTF_8));
                    } else { // config 내장
                        biz.put("sources", srcListToMaps(list));
                        saveConfigFile();
                    }
                    // 캐시 즉시 반영
                    synchronized (CACHE_LOCK) { sourcesCache.put(bizId, list); cacheUpdatedAt.put(bizId, now()); saveCache(); }
                    sendJson(ex, 200, "{\"ok\":true,\"msg\":" + jstr("원천사 " + list.size() + "건 저장 완료 (" + (origin.equals("file") ? "파일" : "config") + ").") + "}");
                    return;
                }

                sendJson(ex, 400, "{\"error\":\"알 수 없는 section (sources|servers|monitor)\"}");
            }
        } catch (Exception e) {
            sendJson(ex, 500, "{\"error\":" + jstr("저장 실패: " + rootMsg(e)) + "}");
        }
    }

    private static String readBody(HttpExchange ex) throws IOException {
        InputStream in = ex.getRequestBody();
        ByteArrayOutputStream b = new ByteArrayOutputStream();
        byte[] t = new byte[4096]; int n;
        while ((n = in.read(t)) > 0) b.write(t, 0, n);
        return new String(b.toByteArray(), StandardCharsets.UTF_8);
    }

    /** config(메모리) 를 파일로 저장. _comment 등은 일반 필드라 그대로 보존됨. CONFIG_LOCK 안에서 호출. */
    private static void saveConfigFile() throws Exception {
        String txt = jsonPretty(config, "") + "\n";
        Files.write(cfgFile.toPath(), txt.getBytes(StandardCharsets.UTF_8));
        // 메모리 참조 갱신 (config 자체는 그대로지만 파생 참조 재설정)
        sshCfg = asMap(config.get("ssh"));
        envCfg = asMap(config.get("env"));
        businessesCfg = asList(config.get("businesses"));
    }

    /** 원천사 리스트 -> 외부 파일용 JSON ({sources:[{id,name,sends:[...],recvs:[...]}]}). */
    private static String sourcesFileJson(List<Src> list) {
        StringBuilder sb = new StringBuilder("{\n  \"sources\": [\n");
        for (int i = 0; i < list.size(); i++) {
            Src s = list.get(i);
            List<Ep> sends = sendsOf(s), recvs = recvsOf(s);
            if (i > 0) sb.append(",\n");
            sb.append("    { \"id\": ").append(jstr(s.id)).append(", \"name\": ").append(jstr(s.name)).append(",\n");
            sb.append("      \"sends\": [");
            for (int j = 0; j < sends.size(); j++) {
                Ep e = sends.get(j);
                if (j > 0) sb.append(", ");
                sb.append("{ \"label\": ").append(jstr(e.label))
                  .append(", \"sendip\": ").append(jstr(e.sendip))
                  .append(", \"sendport\": ").append(jstr(e.sendport))
                  .append(", \"checkMode\": ").append(jstr(e.checkMode))
                  .append(", \"expectSend\": ").append(e.expectSend).append(" }");
            }
            sb.append("],\n      \"recvs\": [");
            for (int j = 0; j < recvs.size(); j++) {
                Ep e = recvs.get(j);
                if (j > 0) sb.append(", ");
                sb.append("{ \"label\": ").append(jstr(e.label))
                  .append(", \"recvport\": ").append(jstr(e.recvport))
                  .append(", \"expectRecv\": ").append(e.expectRecv).append(" }");
            }
            sb.append("] }");
        }
        sb.append("\n  ]\n}\n");
        return sb.toString();
    }

    /** 원천사 리스트 -> config 내장용 List<Map> (endpoints 정규형). */
    private static List<Object> srcListToMaps(List<Src> list) {
        List<Object> out = new ArrayList<Object>();
        for (Src s : list) {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("id", s.id);
            m.put("name", s.name);
            List<Object> sends = new ArrayList<Object>();
            for (Ep e : sendsOf(s)) {
                Map<String, Object> em = new LinkedHashMap<String, Object>();
                em.put("label", e.label);
                em.put("sendip", e.sendip);
                em.put("sendport", e.sendport);
                em.put("checkMode", e.checkMode);
                em.put("expectSend", e.expectSend);
                sends.add(em);
            }
            List<Object> recvs = new ArrayList<Object>();
            for (Ep e : recvsOf(s)) {
                Map<String, Object> em = new LinkedHashMap<String, Object>();
                em.put("label", e.label);
                em.put("recvport", e.recvport);
                em.put("expectRecv", e.expectRecv);
                recvs.add(em);
            }
            m.put("sends", sends);
            m.put("recvs", recvs);
            out.add(m);
        }
        return out;
    }

    /** 임의 객체(Map/List/String/Number/Boolean/null) -> 들여쓴 JSON. 정수형 Double 은 정수로 출력(포트/주기 보존). */
    @SuppressWarnings("unchecked")
    private static String jsonPretty(Object o, String indent) {
        if (o == null) return "null";
        if (o instanceof Boolean) return String.valueOf(o);
        if (o instanceof Number) {
            double d = ((Number) o).doubleValue();
            if (d == Math.floor(d) && !Double.isInfinite(d)) return String.valueOf((long) d);
            return String.valueOf(d);
        }
        if (o instanceof String) return jstr((String) o);
        if (o instanceof Map) {
            Map<String, Object> m = (Map<String, Object>) o;
            if (m.isEmpty()) return "{}";
            String ni = indent + "  ";
            StringBuilder sb = new StringBuilder("{\n");
            int i = 0;
            for (Map.Entry<String, Object> e : m.entrySet()) {
                if (i++ > 0) sb.append(",\n");
                sb.append(ni).append(jstr(e.getKey())).append(": ").append(jsonPretty(e.getValue(), ni));
            }
            return sb.append("\n").append(indent).append("}").toString();
        }
        if (o instanceof List) {
            List<Object> a = (List<Object>) o;
            if (a.isEmpty()) return "[]";
            String ni = indent + "  ";
            StringBuilder sb = new StringBuilder("[\n");
            for (int i = 0; i < a.size(); i++) {
                if (i > 0) sb.append(",\n");
                sb.append(ni).append(jsonPretty(a.get(i), ni));
            }
            return sb.append("\n").append(indent).append("]").toString();
        }
        return jstr(String.valueOf(o));
    }

    // ---------------------------------------------------------------------
    // 원천사 출처 로딩 (파일 / config / DB)
    // ---------------------------------------------------------------------

    /** biz id 로 업무 config 조회. 없거나 id 미지정이면 첫 업무 반환. */
    private static Map<String, Object> bizById(String id) {
        if (id != null && !id.isEmpty()) {
            for (Object o : businessesCfg) {
                Map<String, Object> b = asMap(o);
                if (str(b.get("id"), "").equals(id)) return b;
            }
        }
        return businessesCfg.isEmpty() ? new LinkedHashMap<String, Object>() : asMap(businessesCfg.get(0));
    }

    /**
     * 원천사 출처 종류: file(외부파일 주입) / config(내장) / db(Oracle) / none.
     * sourceMode 가 명시돼 있으면 그 값을 우선 사용(자동 우선순위 오버라이드).
     * → DB 접속정보(oracle)를 저장해 둔 채로도 지금은 file/config 를 쓰도록 고정할 수 있음.
     */
    private static String sourceType(Map<String, Object> biz) {
        String mode = str(biz.get("sourceMode"), "").trim();
        if (mode.equals("file") || mode.equals("config") || mode.equals("db")) return mode;
        // 자동(우선순위): sourcesFile > sources > oracle.sourcesSql
        if (!str(biz.get("sourcesFile"), "").trim().isEmpty()) return "file";
        if (biz.get("sources") != null) return "config";
        if (!str(asMap(biz.get("oracle")).get("sourcesSql"), "").trim().isEmpty()) return "db";
        return "none";
    }

    /** 화면 표시용 출처 참조(파일경로 / config내장 / DB주소). */
    private static String sourceRef(Map<String, Object> biz) {
        String t = sourceType(biz);
        if (t.equals("file")) return str(biz.get("sourcesFile"), "");
        if (t.equals("config")) return "config 내장 (" + asList(biz.get("sources")).size() + "건)";
        if (t.equals("db")) return dbShort(str(asMap(biz.get("oracle")).get("url"), ""));
        return "";
    }

    private static String dbShort(String url) {
        return String.valueOf(url == null ? "" : url).replaceFirst("(?i)^jdbc:oracle:thin:@/*", "");
    }

    /** sourceType(sourceMode 우선, 없으면 파일>config>DB) 에 따라 원천사 로드. */
    private static List<Src> resolveSources(Map<String, Object> biz) throws Exception {
        String type = sourceType(biz);
        // (a) 외부 파일 주입 — 매 호출마다 파일을 다시 읽으므로 재시작 없이 반영됨
        if (type.equals("file")) {
            String file = str(biz.get("sourcesFile"), "").trim();
            if (file.isEmpty()) throw new Exception("파일 방식인데 sourcesFile 경로가 없습니다.");
            File f = new File(file);
            if (!f.isAbsolute()) f = new File(baseDir, file);
            if (!f.isFile()) throw new Exception("sourcesFile 을 찾을 수 없습니다: " + f.getAbsolutePath());
            String txt = new String(Files.readAllBytes(f.toPath()), StandardCharsets.UTF_8);
            return parseSourcesText(txt);
        }
        // (b) config 내장 — 재갱신 시 config 파일을 다시 읽어 최신 편집 반영
        if (type.equals("config")) {
            Map<String, Object> live = reloadBizFromConfig(str(biz.get("id"), ""));
            Object srcObj = (live != null && live.get("sources") != null) ? live.get("sources") : biz.get("sources");
            return parseSourcesList(asList(srcObj));
        }
        // (c) Oracle DB
        if (type.equals("db")) {
            Map<String, Object> oracle = asMap(biz.get("oracle"));
            if (str(oracle.get("sourcesSql"), "").trim().isEmpty()) throw new Exception("DB 방식인데 oracle.sourcesSql 이 없습니다.");
            return querySources(oracle);
        }
        throw new Exception("원천사 출처가 없습니다. businesses 항목에 sourcesFile / sources / oracle.sourcesSql 중 하나를 설정하거나 sourceMode 를 지정하세요.");
    }

    /** config 파일을 다시 읽어 해당 biz 를 반환 (config 직접 편집 반영용). 실패하면 null. */
    private static Map<String, Object> reloadBizFromConfig(String id) {
        try {
            if (cfgFile == null || !cfgFile.isFile() || id == null || id.isEmpty()) return null;
            String txt = new String(Files.readAllBytes(cfgFile.toPath()), StandardCharsets.UTF_8);
            Map<String, Object> root = asMap(Json.parse(txt));
            for (Object o : asList(root.get("businesses"))) {
                Map<String, Object> b = asMap(o);
                if (id.equals(str(b.get("id"), ""))) return b;
            }
        } catch (Exception ignore) {}
        return null;
    }

    /** 외부 파일 텍스트 파싱: 배열 [...] 또는 { "sources":[...] } 모두 허용. */
    private static List<Src> parseSourcesText(String txt) {
        Object root = Json.parse(txt);
        List<Object> arr;
        if (root instanceof List) arr = asList(root);
        else arr = asList(asMap(root).get("sources"));
        return parseSourcesList(arr);
    }

    /**
     * JSON 배열 -> Src 리스트. 송신/수신 분리 모델(sends[]/recvs[]) 우선,
     * 없으면 레거시 endpoints[](송+수 결합) 또는 flat 을 자동으로 송·수신으로 분리해 담는다.
     * 내부적으로 Src.endpoints 의 각 Ep 은 '순수 송신' 또는 '순수 수신' 이다(수신 Ep 은 recvport 만).
     */
    private static List<Src> parseSourcesList(List<Object> arr) {
        List<Src> out = new ArrayList<Src>();
        for (Object o : arr) {
            Map<String, Object> m = asMap(o);
            Src s = new Src();
            s.id = nz(str(m.get("id"), ""));
            s.name = str(m.get("name"), s.id);
            String srcMode = str(m.get("checkMode"), str(m.get("mode"), ""));
            List<Object> sends = asList(m.get("sends"));
            List<Object> recvs = asList(m.get("recvs"));
            List<Object> eps = asList(m.get("endpoints"));

            if (!sends.isEmpty() || !recvs.isEmpty()) {
                // 새 분리 모델
                for (Object so : sends) {
                    Map<String, Object> em = asMap(so);
                    Ep e = new Ep();
                    e.label = nz(str(em.get("label"), ""));
                    e.sendip = nz(str(em.get("sendip"), ""));
                    e.sendport = nz(str(em.get("sendport"), ""));
                    e.checkMode = toCheckMode(str(em.get("checkMode"), str(em.get("mode"), srcMode.isEmpty() ? "session" : srcMode)));
                    e.expectSend = (int) num(em.get("expectSend"), 0);
                    if (e.hasSend()) s.endpoints.add(e);
                }
                for (Object ro : recvs) {
                    Map<String, Object> em = asMap(ro);
                    Ep e = new Ep();
                    e.label = nz(str(em.get("label"), ""));
                    e.recvport = nz(str(em.get("recvport"), ""));
                    e.expectRecv = (int) num(em.get("expectRecv"), 0);
                    if (e.hasRecv()) s.endpoints.add(e);
                }
            } else if (!eps.isEmpty()) {
                // 레거시 endpoints(송+수 결합) → 송신 Ep + 수신 Ep 로 분리(수신 포트 중복 제거)
                String srcRecv = nz(str(m.get("recvport"), ""));
                java.util.Set<String> recvSeen = new java.util.HashSet<String>();
                for (Object eo : eps) {
                    Map<String, Object> em = asMap(eo);
                    String lab = nz(str(em.get("label"), ""));
                    String sip = nz(str(em.get("sendip"), "")), spt = nz(str(em.get("sendport"), ""));
                    String rpt = nz(str(em.get("recvport"), srcRecv));
                    String cm = toCheckMode(str(em.get("checkMode"), str(em.get("mode"), srcMode.isEmpty() ? "session" : srcMode)));
                    if (!sip.isEmpty() && !spt.isEmpty()) {
                        Ep e = new Ep(); e.label = lab; e.sendip = sip; e.sendport = spt; e.checkMode = cm;
                        e.expectSend = (int) num(em.get("expectSend"), 0); s.endpoints.add(e);
                    }
                    if (!rpt.isEmpty() && recvSeen.add(rpt)) {
                        Ep e = new Ep(); e.label = lab; e.recvport = rpt;
                        e.expectRecv = (int) num(em.get("expectRecv"), 0); s.endpoints.add(e);
                    }
                }
            } else {
                // 레거시 flat
                String sip = nz(str(m.get("sendip"), "")), spt = nz(str(m.get("sendport"), "")), rpt = nz(str(m.get("recvport"), ""));
                if (!sip.isEmpty() && !spt.isEmpty()) {
                    Ep e = new Ep(); e.sendip = sip; e.sendport = spt;
                    e.checkMode = toCheckMode(srcMode.isEmpty() ? "session" : srcMode);
                    e.expectSend = (int) num(m.get("expectSend"), 0); s.endpoints.add(e);
                }
                if (!rpt.isEmpty()) {
                    Ep e = new Ep(); e.recvport = rpt; e.expectRecv = (int) num(m.get("expectRecv"), 0); s.endpoints.add(e);
                }
            }
            if (!s.id.isEmpty()) out.add(s);
        }
        return out;
    }

    /** Src 의 순수-송신 엔드포인트 목록. */
    private static List<Ep> sendsOf(Src s) { List<Ep> r = new ArrayList<Ep>(); for (Ep e : s.endpoints) if (e.hasSend()) r.add(e); return r; }
    /** Src 의 순수-수신 엔드포인트 목록. */
    private static List<Ep> recvsOf(Src s) { List<Ep> r = new ArrayList<Ep>(); for (Ep e : s.endpoints) if (e.hasRecv() && !e.hasSend()) r.add(e); return r; }

    private static Connection openDb(Map<String, Object> oracle) throws Exception {
        String url = str(oracle.get("url"), null);
        String user = str(oracle.get("user"), null);
        String pass = str(oracle.get("password"), null);
        Properties p = new Properties();
        if (user != null) p.put("user", user);
        if (pass != null) p.put("password", pass);
        // 느리거나 불통인 DB 에 무한정 매달리지 않도록 타임아웃 (ms)
        p.put("oracle.net.CONNECT_TIMEOUT", "8000");   // TCP/접속 8초
        p.put("oracle.jdbc.ReadTimeout", "20000");     // 쿼리 응답 20초
        DriverManager.setLoginTimeout(10);             // 로그인 10초
        return DriverManager.getConnection(url, p);
    }

    /**
     * DB 조회. id 로 그룹핑하고, 각 행을 '송신 Ep' 와 '수신 Ep' 로 분리해 담는다(수신 포트 중복 제거).
     * sourcesSql 은 id,name,sendip,sendport,recvport (선택: label, mode, expectsend, expectrecv) alias 반환.
     * mode 컬럼 값이 S/A 면 동기/비동기로 보고 자동 매핑: A=session(연결유지), S=skip(제외).
     */
    private static List<Src> querySources(Map<String, Object> oracle) throws Exception {
        String sql = str(oracle.get("sourcesSql"), null);
        LinkedHashMap<String, Src> byId = new LinkedHashMap<String, Src>();
        LinkedHashMap<String, java.util.Set<String>> recvSeen = new LinkedHashMap<String, java.util.Set<String>>();
        boolean hasLabel = true, hasMode = true, hasExpSend = true, hasExpRecv = true;
        Connection c = null; Statement st = null; ResultSet rs = null;
        try {
            c = openDb(oracle);
            st = c.createStatement();
            rs = st.executeQuery(sql);
            while (rs.next()) {
                String id = nz(rs.getString("id"));
                if (id.isEmpty()) continue;
                Src s = byId.get(id);
                if (s == null) { s = new Src(); s.id = id; s.name = nz(rs.getString("name")); byId.put(id, s); recvSeen.put(id, new java.util.HashSet<String>()); }
                String sip = nz(rs.getString("sendip")), spt = nz(rs.getString("sendport")), rpt = nz(rs.getString("recvport"));
                String label = "";
                if (hasLabel) { try { label = nz(rs.getString("label")); } catch (Exception e) { hasLabel = false; } }
                String cm = "session";
                if (hasMode) { try { cm = toCheckMode(nz(rs.getString("mode"))); } catch (Exception e) { hasMode = false; } }
                // DB 조회는 예상 세션수 기본값 2(송신·수신). expectsend/expectrecv 컬럼이 있으면 그 값 사용.
                int expS = 2, expR = 2;
                if (hasExpSend) { try { expS = rs.getInt("expectsend"); } catch (Exception e) { hasExpSend = false; expS = 2; } }
                if (hasExpRecv) { try { expR = rs.getInt("expectrecv"); } catch (Exception e) { hasExpRecv = false; expR = 2; } }
                if (!sip.isEmpty() && !spt.isEmpty()) {
                    Ep e = new Ep(); e.label = label; e.sendip = sip; e.sendport = spt; e.checkMode = cm; e.expectSend = expS; s.endpoints.add(e);
                }
                if (!rpt.isEmpty() && recvSeen.get(id).add(rpt)) {
                    Ep e = new Ep(); e.label = label; e.recvport = rpt; e.expectRecv = expR; s.endpoints.add(e);
                }
            }
        } finally { closeAll(rs, st, c); }
        return new ArrayList<Src>(byId.values());
    }

    /** 캐시에서 biz + id 로 원천사 조회 */
    private static Src findInCache(String bizId, String id) {
        synchronized (CACHE_LOCK) {
            List<Src> list = sourcesCache.get(bizId);
            if (list == null) return null;
            for (Src s : list) {
                if (id.equals(s.id)) return s;
            }
            return null;
        }
    }

    // -------------------------- 캐시 영속화 (JSON 파일) --------------------------

    private static void loadCache() {
        try {
            if (cacheFile == null || !cacheFile.isFile()) return;
            String txt = new String(Files.readAllBytes(cacheFile.toPath()), StandardCharsets.UTF_8);
            Map<String, Object> root = asMap(Json.parse(txt));
            for (Map.Entry<String, Object> e : root.entrySet()) {
                Map<String, Object> b = asMap(e.getValue());
                sourcesCache.put(e.getKey(), parseSourcesList(asList(b.get("sources"))));
                cacheUpdatedAt.put(e.getKey(), str(b.get("updatedAt"), ""));
            }
            System.out.println("[cache] 로드: " + cacheFile.getName() + " (업무 " + sourcesCache.size() + ")");
        } catch (Exception e) {
            System.out.println("[cache] 로드 실패 (무시하고 빈 캐시로 시작): " + rootMsg(e));
        }
    }

    /** CACHE_LOCK 안에서 호출할 것 */
    private static void saveCache() {
        try {
            StringBuilder sb = new StringBuilder("{\n");
            int bi = 0;
            for (Map.Entry<String, List<Src>> e : sourcesCache.entrySet()) {
                if (bi++ > 0) sb.append(",\n");
                sb.append("  ").append(jstr(e.getKey())).append(": {\"updatedAt\":")
                  .append(jstr(str(cacheUpdatedAt.get(e.getKey()), ""))).append(",\"sources\":[");
                List<Src> list = e.getValue();
                for (int i = 0; i < list.size(); i++) {
                    if (i > 0) sb.append(',');
                    sb.append(sourceJson(list.get(i)));
                }
                sb.append("]}");
            }
            sb.append("\n}\n");
            Files.write(cacheFile.toPath(), sb.toString().getBytes(StandardCharsets.UTF_8));
        } catch (Exception e) {
            System.out.println("[cache] 저장 실패: " + rootMsg(e));
        }
    }

    private static String now() {
        return new java.text.SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new java.util.Date());
    }

    // -------------------------- 조회 이력 --------------------------

    private static void recordHistory(Map<String, Object> entry) {
        synchronized (history) {
            history.addFirst(entry);
            while (history.size() > HISTORY_MAX) history.removeLast();
            saveHistory();
        }
    }

    /** JSON 스칼라 직렬화 (String/Number/Boolean) */
    private static String jval(Object o) {
        if (o == null) return "null";
        if (o instanceof Boolean || o instanceof Number) return String.valueOf(o);
        return jstr(String.valueOf(o));
    }

    private static String entryJson(Map<String, Object> e) {
        StringBuilder sb = new StringBuilder("{");
        int i = 0;
        for (Map.Entry<String, Object> kv : e.entrySet()) {
            if (i++ > 0) sb.append(',');
            sb.append(jstr(kv.getKey())).append(':').append(jval(kv.getValue()));
        }
        return sb.append('}').toString();
    }

    /** history -> {"entries":[...]} (CACHE 형태와 무관, history 락 안/밖 모두 안전하게 스냅샷 사용) */
    private static String historyJson() {
        StringBuilder sb = new StringBuilder("{\"entries\":[");
        synchronized (history) {
            int i = 0;
            for (Map<String, Object> e : history) {
                if (i++ > 0) sb.append(',');
                sb.append(entryJson(e));
            }
        }
        return sb.append("]}").toString();
    }

    private static void saveHistory() {
        try { Files.write(historyFile.toPath(), historyJson().getBytes(StandardCharsets.UTF_8)); }
        catch (Exception e) { System.out.println("[history] 저장 실패: " + rootMsg(e)); }
    }

    private static void loadHistory() {
        try {
            if (historyFile == null || !historyFile.isFile()) return;
            String txt = new String(Files.readAllBytes(historyFile.toPath()), StandardCharsets.UTF_8);
            Map<String, Object> root = asMap(Json.parse(txt));
            for (Object o : asList(root.get("entries"))) {
                Map<String, Object> src = asMap(o);
                Map<String, Object> e = new LinkedHashMap<String, Object>();
                for (Map.Entry<String, Object> kv : src.entrySet()) e.put(kv.getKey(), kv.getValue());
                history.addLast(e);   // 파일은 최신순 저장 -> 순서 유지
            }
            System.out.println("[history] 로드: " + historyFile.getName() + " (" + history.size() + "건)");
        } catch (Exception e) {
            System.out.println("[history] 로드 실패 (무시): " + rootMsg(e));
        }
    }

    private static String statusKo(String st) {
        if ("ok".equals(st)) return "정상";
        if ("excess".equals(st)) return "초과";
        if ("short".equals(st)) return "부족";
        if ("warn".equals(st)) return "주의";
        if ("bad".equals(st)) return "장애";
        return "-";
    }

    /** 원천사 클러스터(서버 전체) 합산 상태. sendState/recvState: na/ok/mismatch/absent. */
    static class SrcStat {
        String status = "mut";
        String sendState = "na", recvState = "na";
        int errCnt = 0;
        boolean sendApp = false, recvApp = false;
        int sendTotal = 0, sendNeed = 0, recvTotal = 0, recvNeed = 0;
    }

    /**
     * 원천사 종합 상태를 '클러스터(서버 전체) 합산' 으로 판정한다.
     * 세션이 어느 서버에 있든, 엔드포인트별로 서버 전체를 합산해 기대 세션수와 비교:
     *   - 설정값(expect>0)이 있으면 '정확히 일치'해야 정상. 부족/초과면 주의(warn).
     *   - 설정값이 없으면(미지정) 1개 이상이면 정상.
     * 색: 모두 일치=ok(초록), 부족/초과 섞임=mismatch=warn(노랑), 완전 없음=absent=bad(빨강).
     */
    private static SrcStat computeSrcStat(List<CheckResult> results) {
        SrcStat st = new SrcStat();
        int M = results.size();
        // sendkey -> [expect(>0 명시, -1 미지정), total, probe(0/1)]
        LinkedHashMap<String, int[]> sendAgg = new LinkedHashMap<String, int[]>();
        // recvport -> [expect(>0 명시, -1 미지정), total, anyListen(0/1)]
        LinkedHashMap<String, int[]> recvAgg = new LinkedHashMap<String, int[]>();
        for (CheckResult r : results) {
            if (!r.ok) { st.errCnt++; continue; }
            // 같은 서버 안에서 동일 키(sendip:sendport / recvport)는 세션수를 한 번만 합산(중복 줄 방지).
            java.util.Set<String> seenSend = new java.util.HashSet<String>();
            java.util.Set<String> seenRecv = new java.util.HashSet<String>();
            for (EpResult er : r.eps) {
                if (er.sendChecked()) {
                    String k = er.sendip + ":" + er.sendport;
                    int expThis = er.isProbe() ? 0 : (er.expectSend > 0 ? er.expectSend : -1);
                    int[] a = sendAgg.get(k);
                    if (a == null) sendAgg.put(k, a = new int[]{ expThis, 0, er.isProbe() ? 1 : 0 });
                    else { if (expThis > 0) a[0] = (a[0] > 0 ? Math.max(a[0], expThis) : expThis); if (er.isProbe()) a[2] = 1; }
                    if (seenSend.add(k)) a[1] += er.sendCount;   // 서버당 같은 키 1회만
                }
                if (er.hasRecv()) {
                    String p = er.recvport;
                    int expThis = er.expectRecv > 0 ? er.expectRecv : -1;
                    int[] b = recvAgg.get(p);
                    if (b == null) recvAgg.put(p, b = new int[]{ expThis, 0, 0 });
                    else if (expThis > 0) b[0] = (b[0] > 0 ? Math.max(b[0], expThis) : expThis);
                    if (er.recvListening) b[2] = 1;
                    if (seenRecv.add(p)) b[1] += er.recvEstabCount;   // 서버당 같은 포트 1회만
                }
            }
        }
        st.sendApp = !sendAgg.isEmpty();
        st.recvApp = !recvAgg.isEmpty();
        // 엔드포인트별 상태: 0=OK(정확), 1=EXCESS(초과), 2=SHORT(부족), 3=ABSENT(없음)
        int sOk = 0, sExc = 0, sSht = 0, sAbs = 0, sN = 0;
        for (int[] a : sendAgg.values()) {
            int exp = a[0], total = a[1], probe = a[2];
            st.sendTotal += total; st.sendNeed += (exp > 0 ? exp : 1);
            int state;
            if (total == 0) state = 3;                              // 없음
            else if (probe == 1) state = 0;                         // probe 열림 → 정상(초과 개념 없음)
            else if (exp > 0) state = (total == exp) ? 0 : (total > exp ? 1 : 2);   // 초과/부족
            else state = 0;                                         // 미지정: 붙어있으면 정상
            if (state == 0) sOk++; else if (state == 1) sExc++; else if (state == 2) sSht++; else sAbs++;
            sN++;
        }
        int rOk = 0, rExc = 0, rSht = 0, rAbs = 0, rN = 0;
        for (int[] b : recvAgg.values()) {
            int exp = b[0], total = b[1], lis = b[2];
            st.recvTotal += total; st.recvNeed += (exp > 0 ? exp : 0);
            int state;
            if (lis == 0) state = 3;                                // 닫힘/없음
            else if (exp > 0) state = (total == exp) ? 0 : (total > exp ? 1 : 2);
            else state = 0;                                         // 미지정: 리슨이면 정상
            if (state == 0) rOk++; else if (state == 1) rExc++; else if (state == 2) rSht++; else rAbs++;
            rN++;
        }
        st.sendState = axisState(sN, sOk, sExc, sSht, sAbs);
        st.recvState = axisState(rN, rOk, rExc, rSht, rAbs);

        if (M == 0 || (st.sendState.equals("na") && st.recvState.equals("na"))) { st.status = "mut"; return st; }
        int sev = Math.max(stateSev(st.sendState), stateSev(st.recvState));
        if (st.errCnt > 0) sev = Math.max(sev, 3);                  // 서버 점검 실패 → 최소 부족(주황)
        st.status = sevStatus(sev);
        return st;
    }

    /** 축(송신/수신) 종합 상태. 전부없음=absent, 전부일치=ok, 부족/일부없음=short, 나머지(초과만)=excess. */
    private static String axisState(int n, int ok, int exc, int sht, int abs) {
        if (n == 0) return "na";
        if (abs == n) return "absent";
        if (ok == n) return "ok";
        if (sht > 0 || abs > 0) return "short";   // 부족하거나 일부 완전 없음
        return "excess";                          // 나머지는 초과만
    }
    private static int stateSev(String s) {
        if ("absent".equals(s)) return 4;
        if ("short".equals(s)) return 3;
        if ("excess".equals(s)) return 2;
        if ("ok".equals(s)) return 1;
        return 0;   // na
    }
    private static String sevStatus(int sev) {
        return sev >= 4 ? "bad" : (sev == 3 ? "short" : (sev == 2 ? "excess" : (sev == 1 ? "ok" : "mut")));
    }

    /** 상태 요약 문자열 (송신 실제/기대 · 수신 실제/기대 · 실패). */
    private static String statSummary(SrcStat st) {
        List<String> parts = new ArrayList<String>();
        if (st.sendApp) parts.add("송신 " + st.sendTotal + "/" + st.sendNeed);
        if (st.recvApp) parts.add("수신 " + st.recvTotal + "/" + st.recvNeed);
        if (st.errCnt > 0) parts.add("실패 " + st.errCnt);
        if (parts.isEmpty()) return "점검 대상 없음";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < parts.size(); i++) { if (i > 0) sb.append(" · "); sb.append(parts.get(i)); }
        return sb.toString();
    }

    private static boolean truthy(String s) {
        return s != null && (s.equals("1") || s.equalsIgnoreCase("true") || s.equalsIgnoreCase("yes"));
    }

    // ---------------------------------------------------------------------
    // SSH check (ss / netstat 로 ESTABLISHED 세션 존재 여부)
    // ---------------------------------------------------------------------

    /** 엔드포인트 1개의 서버 1대에 대한 점검 결과. */
    static class EpResult {
        String label = "", sendip = "", sendport = "", recvport = "";
        String mode = "session";            // session / probe / skip
        int expectSend = 0, expectRecv = 0; // 예상 세션수(0=미지정)
        boolean sendConnected = false;      // 송신 정상(기대 세션수 충족). session: 세션수≥기대 / probe: OPEN
        int sendCount = 0;                  // session: 세션 개수 / probe: 1(열림) or 0
        boolean probeOpen = false;          // probe 모드 결과
        boolean recvListening = false;      // 수신 포트 LISTEN(대기중)
        boolean recvOk = false;             // 수신 정상(LISTEN + 기대 세션수 충족)
        int recvEstabCount = 0;             // 수신 포트로 붙어있는 ESTABLISHED 세션 수
        List<String> sendLines = new ArrayList<String>();
        List<String> recvListenLines = new ArrayList<String>();
        List<String> recvEstabLines = new ArrayList<String>();

        boolean hasSend() { return !sendip.isEmpty() && !sendport.isEmpty(); }
        boolean hasRecv() { return !recvport.isEmpty(); }
        boolean isSkip() { return "skip".equals(mode); }
        boolean isProbe() { return "probe".equals(mode); }
        boolean sendChecked() { return hasSend() && !isSkip(); }   // skip 이면 송신 판정 안 함

        String toJson() {
            StringBuilder sb = new StringBuilder("{");
            sb.append("\"label\":").append(jstr(label));
            sb.append(",\"sendip\":").append(jstr(sendip));
            sb.append(",\"sendport\":").append(jstr(sendport));
            sb.append(",\"recvport\":").append(jstr(recvport));
            sb.append(",\"mode\":").append(jstr(mode));
            sb.append(",\"expectSend\":").append(expectSend);
            sb.append(",\"expectRecv\":").append(expectRecv);
            sb.append(",\"sendConnected\":").append(sendConnected);
            sb.append(",\"sendCount\":").append(sendCount);
            sb.append(",\"recvListening\":").append(recvListening);
            sb.append(",\"recvOk\":").append(recvOk);
            sb.append(",\"recvEstabCount\":").append(recvEstabCount);
            sb.append(",\"sendLines\":").append(jarr(sendLines));
            sb.append(",\"recvListenLines\":").append(jarr(recvListenLines));
            sb.append(",\"recvEstabLines\":").append(jarr(recvEstabLines));
            return sb.append('}').toString();
        }
    }

    /** 서버 1대에 대한 원천사(여러 엔드포인트) 종합 점검 결과. */
    static class CheckResult {
        String serverId = "";
        String host = "";
        boolean ok = false;                 // SSH/명령 실행 성공 여부
        String error = "";
        List<EpResult> eps = new ArrayList<EpResult>();
        // 집계 (엔드포인트 종합): 송신은 '송신 판정 대상 전부 연결됨', 수신은 '수신 있는 엔드포인트 전부 LISTEN'
        boolean sendConnected = false;
        int sendCount = 0;
        boolean sendApplicable = false;     // 송신 판정 대상이 하나라도 있는가(skip 만 있으면 false)
        boolean recvListening = false;
        int recvEstabCount = 0;
        boolean recvApplicable = false;

        void aggregate() {
            // 송신은 sendip:sendport 기준, 수신은 recvport 기준으로 '유니크'하게 집계한다.
            // → 이중화(송신은 다르지만 수신 포트가 같은) 경우, 같은 수신 포트를 엔드포인트마다
            //   중복으로 세어 개수가 뻥튀기되는 문제를 방지(예: 실제 2개인데 4개로 표시).
            // skip(송신 판정 제외) 엔드포인트는 송신 집계에서 뺀다.
            // 송신: sendip:sendport 기준 유니크(엔드포인트별 구분).
            LinkedHashMap<String, EpResult> sends = new LinkedHashMap<String, EpResult>();
            for (EpResult er : eps) {
                if (er.sendChecked()) { String k = er.sendip + ":" + er.sendport; if (!sends.containsKey(k)) sends.put(k, er); }
            }
            // 수신: recvport 는 하나의 LISTEN 포트 → 포트 단위로 통일. 같은 포트를 여러 엔드포인트가 써도
            // 실제 세션은 한 번만 세고(중복 방지), 기대 세션수(expectRecv)도 합산하지 않고 그 포트의 값(최대)으로 본다.
            LinkedHashMap<String, int[]> recvByPort = new LinkedHashMap<String, int[]>();  // port -> [expect, estab, listen]
            for (EpResult er : eps) {
                if (!er.hasRecv()) continue;
                int[] a = recvByPort.get(er.recvport);
                if (a == null) recvByPort.put(er.recvport, new int[]{ er.expectRecv, er.recvEstabCount, er.recvListening ? 1 : 0 });
                else a[0] = Math.max(a[0], er.expectRecv);   // 포트 단위 기대수(합산 X, 설정된 값 사용)
            }
            sendApplicable = !sends.isEmpty();
            recvApplicable = !recvByPort.isEmpty();
            boolean allSend = true, allRecv = true;
            int sc = 0, rc = 0;
            for (EpResult er : sends.values()) { if (!er.sendConnected) allSend = false; sc += er.sendCount; }
            for (int[] a : recvByPort.values()) {
                int exp = a[0], est = a[1]; boolean lis = a[2] == 1;
                boolean ok = lis && (exp <= 0 || est >= exp);   // LISTEN + 기대 세션수 충족
                if (!ok) allRecv = false;
                rc += est;
            }
            sendConnected = sendApplicable && allSend;
            recvListening = recvApplicable && allRecv;
            sendCount = sc;
            recvEstabCount = rc;
        }

        String toJson() {
            StringBuilder sb = new StringBuilder();
            sb.append("{\"serverId\":").append(jstr(serverId));
            sb.append(",\"host\":").append(jstr(host));
            sb.append(",\"ok\":").append(ok);
            sb.append(",\"sendConnected\":").append(sendConnected);
            sb.append(",\"sendCount\":").append(sendCount);
            sb.append(",\"sendApplicable\":").append(sendApplicable);
            sb.append(",\"recvListening\":").append(recvListening);
            sb.append(",\"recvEstabCount\":").append(recvEstabCount);
            sb.append(",\"recvApplicable\":").append(recvApplicable);
            sb.append(",\"error\":").append(jstr(error));
            sb.append(",\"endpoints\":[");
            for (int i = 0; i < eps.size(); i++) { if (i > 0) sb.append(','); sb.append(eps.get(i).toJson()); }
            sb.append("]}");
            return sb.toString();
        }
    }

    private static String jarr(List<String> lines) {
        StringBuilder sb = new StringBuilder("[");
        for (int i = 0; i < lines.size(); i++) {
            if (i > 0) sb.append(',');
            sb.append(jstr(lines.get(i)));
        }
        return sb.append(']').toString();
    }

    // 한 엔드포인트의 관련 라인 grep 정규식.
    // 송신은 'session' 방식만 ss 로 잡는다(probe 는 능동접속, skip 은 제외). 수신은 방식 무관 항상.
    private static String epRx(Ep e) {
        boolean sessSend = e.hasSend() && "session".equals(e.checkMode);
        String sendRx = !sessSend ? "" : e.sendip.replace(".", "\\.") + "[:.]" + e.sendport;
        String recvRx = !e.hasRecv() ? "" : "[:.]" + e.recvport + "([^0-9]|$)";
        if (!sendRx.isEmpty() && !recvRx.isEmpty()) return sendRx + "|" + recvRx;
        return sendRx + recvRx;
    }

    // 한 원천사(모든 엔드포인트) union grep 정규식
    private static String srcRx(Src s) {
        StringBuilder rx = new StringBuilder();
        for (Ep e : s.endpoints) {
            String one = epRx(e);
            if (one.isEmpty()) continue;
            if (rx.length() > 0) rx.append("|");
            rx.append(one);
        }
        return rx.toString();
    }

    // probe 방식 엔드포인트의 "ip:port" 목록 (능동 TCP 접속시도 대상)
    private static List<String> srcProbes(Src s) {
        List<String> out = new ArrayList<String>();
        for (Ep e : s.endpoints) if (e.hasSend() && e.isProbe()) out.add(e.sendip + ":" + e.sendport);
        return out;
    }

    // ss/netstat 명령 + probe(능동 TCP 접속) 명령. relRx 로 서버에서 필터, probe 는 PROBE ip:port OPEN|CLOSED 출력.
    private static String buildCmd(String relRx, List<String> probes) {
        String relGrep = (relRx == null || relRx.isEmpty()) ? "" : " | grep -E '" + relRx + "'";
        StringBuilder cmd = new StringBuilder("( ss -tan 2>/dev/null || netstat -an 2>/dev/null ) | grep -iE 'estab|listen'").append(relGrep);
        if (probes != null) {
            for (String p : probes) {
                int i = p.lastIndexOf(':');
                if (i < 0) continue;
                String ip = p.substring(0, i), port = p.substring(i + 1);
                // nc 우선(-z -w2), 없으면 bash /dev/tcp (timeout 2). 결과: PROBE ip:port OPEN|CLOSED
                cmd.append("; if ( command -v nc >/dev/null 2>&1 && nc -z -w2 ").append(ip).append(" ").append(port)
                   .append(" >/dev/null 2>&1 ) || ( timeout 2 bash -c 'exec 3<>/dev/tcp/").append(ip).append("/").append(port)
                   .append("' >/dev/null 2>&1 ); then echo 'PROBE ").append(p).append(" OPEN'; else echo 'PROBE ").append(p).append(" CLOSED'; fi");
            }
        }
        return cmd.toString();
    }

    // 출력 라인들을 한 엔드포인트 기준으로 분류해 er 에 채움. 방식(session/probe/skip)에 따라 송신 판정이 다름.
    private static void classifyEp(EpResult er, String out) {
        boolean sessSend = er.sendChecked() && "session".equals(er.mode);
        for (String line : out.split("\\r?\\n")) {
            String t = line.trim();
            if (t.isEmpty()) continue;

            // probe 결과 라인
            if (er.isProbe() && er.hasSend() && t.startsWith("PROBE ")) {
                String key = er.sendip + ":" + er.sendport;
                if (t.equals("PROBE " + key + " OPEN")) { er.probeOpen = true; if (!er.sendLines.contains(key + " OPEN")) er.sendLines.add(key + " OPEN"); }
                else if (t.equals("PROBE " + key + " CLOSED")) { if (!er.sendLines.contains(key + " CLOSED")) er.sendLines.add(key + " CLOSED"); }
                continue;
            }

            boolean listen = t.toUpperCase().contains("LISTEN");
            boolean estab = !listen && t.toUpperCase().contains("ESTAB");
            if (!listen && !estab) continue;

            List<String> addrs = addrsOf(t);
            if (addrs.isEmpty()) continue;
            String local = addrs.get(0);
            String peer = addrs.size() >= 2 ? addrs.get(addrs.size() - 1) : null;
            String localPort = portOf(local);

            if (sessSend && estab && peer != null && addrMatches(peer, er.sendip, er.sendport)) {
                if (!er.sendLines.contains(t)) er.sendLines.add(t);
            }
            if (er.hasRecv() && er.recvport.equals(localPort)) {
                if (listen) { if (!er.recvListenLines.contains(t)) er.recvListenLines.add(t); }
                else if (estab) { if (!er.recvEstabLines.contains(t)) er.recvEstabLines.add(t); }
            }
        }
        // 송신 결과 (방식별). session 은 기대 세션수(expectSend) 충족 여부까지 본다.
        if (er.isSkip() || !er.hasSend()) { er.sendConnected = false; er.sendCount = 0; }
        else if (er.isProbe()) { er.sendConnected = er.probeOpen; er.sendCount = er.probeOpen ? 1 : 0; }
        else { er.sendCount = er.sendLines.size(); er.sendConnected = er.sendCount >= (er.expectSend > 0 ? er.expectSend : 1); }
        // 수신 결과. LISTEN(대기중) + 기대 세션수(expectRecv) 충족 여부.
        er.recvListening = !er.recvListenLines.isEmpty();
        er.recvEstabCount = er.recvEstabLines.size();
        er.recvOk = er.recvListening && (er.expectRecv <= 0 || er.recvEstabCount >= er.expectRecv);
    }

    /** 출력으로 원천사의 모든 엔드포인트를 채우고 집계. */
    private static void fillEndpoints(CheckResult r, Src src, String out) {
        r.eps.clear();
        for (Ep e : src.endpoints) {
            EpResult er = new EpResult();
            er.label = e.label; er.sendip = e.sendip; er.sendport = e.sendport; er.recvport = e.recvport;
            er.mode = e.checkMode;
            er.expectSend = e.expectSend; er.expectRecv = e.expectRecv;
            classifyEp(er, out);
            r.eps.add(er);
        }
        r.aggregate();
    }

    private static CheckResult sshCheck(Map<String, Object> srv, Src src) {
        CheckResult r = new CheckResult();
        r.serverId = str(srv.get("id"), "");
        r.host = str(srv.get("host"), "");
        int execTimeout = (int) num(sshCfg.get("execTimeoutSec"), 10) * 1000;
        String cmd = buildCmd(srcRx(src), srcProbes(src));
        try {
            String out = execViaPool(srv, cmd, execTimeout);   // 풀 세션 재사용, 채널만 열어 실행
            fillEndpoints(r, src, out);
            r.ok = true;
        } catch (Exception e) {
            r.ok = false;
            r.error = rootMsg(e);
        }
        return r;
    }

    /** 원천사에 송신 판정 대상(session/probe) 엔드포인트가 하나라도 있는가. */
    private static boolean srcSendApplicable(Src s) { for (Ep e : s.endpoints) if (e.sendChecked()) return true; return false; }
    /** 원천사에 수신 엔드포인트가 하나라도 있는가. */
    private static boolean srcRecvApplicable(Src s) { for (Ep e : s.endpoints) if (e.hasRecv()) return true; return false; }

    // -------------------------- SSH 세션 풀 (재사용) --------------------------
    // 세션은 '버튼(연결 조회/세션 접속)' 눌렀을 때만 lazy 로 연결되고, 이후 살려두고 재사용.
    // 기동 시 자동 접속(워밍업) 안 함.

    private static final Map<String, Session> sshPool = new java.util.concurrent.ConcurrentHashMap<String, Session>();
    private static final Map<String, Object> sshLocks = new java.util.concurrent.ConcurrentHashMap<String, Object>();

    private static String sessionKey(Map<String, Object> srv) {
        return str(srv.get("user"), "") + "@" + str(srv.get("host"), "") + ":" + (int) num(srv.get("sshPort"), 22);
    }

    private static Object lockFor(String key) {
        Object l = sshLocks.get(key);
        if (l == null) { l = new Object(); Object prev = sshLocks.putIfAbsent(key, l); if (prev != null) l = prev; }
        return l;
    }

    /** 풀에서 연결된 세션을 얻음. 없거나 끊겼으면 새로 접속(서버별 락으로 중복접속 방지). */
    private static Session getSession(Map<String, Object> srv) throws Exception {
        String key = sessionKey(srv);
        Session s = sshPool.get(key);
        if (s != null && s.isConnected()) return s;
        synchronized (lockFor(key)) {
            s = sshPool.get(key);
            if (s != null && s.isConnected()) return s;
            if (s != null) { try { s.disconnect(); } catch (Exception ignore) {} }
            String host = str(srv.get("host"), "");
            int sshPort = (int) num(srv.get("sshPort"), 22);
            String user = str(srv.get("user"), "");
            String pass = str(srv.get("password"), "");
            int connTimeout = (int) num(sshCfg.get("connectTimeoutSec"), 6) * 1000;
            JSch jsch = new JSch();
            Session ns = jsch.getSession(user, host, sshPort);
            ns.setPassword(pass);
            Properties p = new Properties();
            p.put("StrictHostKeyChecking", "no");
            ns.setConfig(p);
            ns.setConfig("PreferredAuthentications", "password,keyboard-interactive");
            ns.setServerAliveInterval(30000);   // 30초 keepalive 로 유휴에도 살려둠
            ns.connect(connTimeout);
            sshPool.put(key, ns);
            return ns;
        }
    }

    private static void dropSession(Map<String, Object> srv) {
        Session s = sshPool.remove(sessionKey(srv));
        if (s != null) { try { s.disconnect(); } catch (Exception ignore) {} }
    }

    private static boolean isConnected(Map<String, Object> srv) {
        Session s = sshPool.get(sessionKey(srv));
        return s != null && s.isConnected();
    }

    /** 풀 세션으로 명령 실행. 세션이 죽었으면 1회 재접속 후 재시도. */
    private static String execViaPool(Map<String, Object> srv, String cmd, int execTimeout) throws Exception {
        try {
            return execOnSession(getSession(srv), cmd, execTimeout);
        } catch (Exception first) {
            dropSession(srv);
            return execOnSession(getSession(srv), cmd, execTimeout);
        }
    }

    private static String execOnSession(Session session, String cmd, int execTimeout) throws Exception {
        ChannelExec channel = null;
        try {
            channel = (ChannelExec) session.openChannel("exec");
            channel.setCommand(cmd);
            channel.setErrStream(null);
            InputStream in = channel.getInputStream();
            channel.connect();
            ByteArrayOutputStream buf = new ByteArrayOutputStream();
            byte[] tmp = new byte[2048];
            long deadline = System.currentTimeMillis() + execTimeout;
            while (true) {
                while (in.available() > 0) {
                    int n = in.read(tmp, 0, tmp.length);
                    if (n < 0) break;
                    buf.write(tmp, 0, n);
                }
                if (channel.isClosed()) { if (in.available() > 0) continue; break; }
                if (System.currentTimeMillis() > deadline) break;
                try { Thread.sleep(20); } catch (InterruptedException ie) { break; }
            }
            return new String(buf.toByteArray(), StandardCharsets.UTF_8);
        } finally {
            if (channel != null) channel.disconnect();
        }
    }

    // ---------------------------------------------------------------------
    // HTTP helpers
    // ---------------------------------------------------------------------

    private static void sendJson(HttpExchange ex, int code, String json) throws IOException {
        send(ex, code, "application/json; charset=utf-8", json.getBytes(StandardCharsets.UTF_8));
    }

    private static void send(HttpExchange ex, int code, String ctype, String body) throws IOException {
        send(ex, code, ctype, body.getBytes(StandardCharsets.UTF_8));
    }

    private static void send(HttpExchange ex, int code, String ctype, byte[] body) throws IOException {
        ex.getResponseHeaders().set("Content-Type", ctype);
        ex.sendResponseHeaders(code, body.length);
        OutputStream os = ex.getResponseBody();
        os.write(body);
        os.close();
    }

    private static String param(String rawQuery, String key) {
        if (rawQuery == null) return null;
        for (String kv : rawQuery.split("&")) {
            int i = kv.indexOf('=');
            if (i < 0) continue;
            String k = kv.substring(0, i);
            if (k.equals(key)) {
                try { return URLDecoder.decode(kv.substring(i + 1), "UTF-8"); }
                catch (Exception e) { return kv.substring(i + 1); }
            }
        }
        return null;
    }

    private static String mime(String path) {
        String p = path.toLowerCase();
        if (p.endsWith(".html")) return "text/html; charset=utf-8";
        if (p.endsWith(".css")) return "text/css; charset=utf-8";
        if (p.endsWith(".js")) return "application/javascript; charset=utf-8";
        return "application/octet-stream";
    }

    /** 원천사 -> JSON. 송신/수신 분리(sends/recvs). 하위호환 위해 top-level 첫 송신/수신도 함께 내보냄. */
    private static String sourceJson(Src s) {
        List<Ep> sends = sendsOf(s), recvs = recvsOf(s);
        Ep fs = sends.isEmpty() ? new Ep() : sends.get(0);
        Ep fr = recvs.isEmpty() ? new Ep() : recvs.get(0);
        StringBuilder sb = new StringBuilder("{\"id\":").append(jstr(s.id))
                .append(",\"name\":").append(jstr(s.name))
                .append(",\"sendip\":").append(jstr(fs.sendip))
                .append(",\"sendport\":").append(jstr(fs.sendport))
                .append(",\"recvport\":").append(jstr(fr.recvport))
                .append(",\"sends\":[");
        for (int i = 0; i < sends.size(); i++) {
            Ep e = sends.get(i);
            if (i > 0) sb.append(',');
            sb.append("{\"label\":").append(jstr(e.label))
              .append(",\"sendip\":").append(jstr(e.sendip))
              .append(",\"sendport\":").append(jstr(e.sendport))
              .append(",\"checkMode\":").append(jstr(e.checkMode))
              .append(",\"expectSend\":").append(e.expectSend).append('}');
        }
        sb.append("],\"recvs\":[");
        for (int i = 0; i < recvs.size(); i++) {
            Ep e = recvs.get(i);
            if (i > 0) sb.append(',');
            sb.append("{\"label\":").append(jstr(e.label))
              .append(",\"recvport\":").append(jstr(e.recvport))
              .append(",\"expectRecv\":").append(e.expectRecv).append('}');
        }
        return sb.append("]}").toString();
    }

    // ---------------------------------------------------------------------
    // small utils
    // ---------------------------------------------------------------------

    private static String nz(String s) { return s == null ? "" : s.trim(); }

    // ss/netstat 한 줄에서 주소:포트 처럼 보이는 토큰들을 순서대로 추출.
    // ss ESTAB:  ESTAB 0 0 LOCAL PEER          -> [LOCAL, PEER]
    // ss LISTEN: LISTEN 0 128 0.0.0.0:7000 *:* -> [LOCAL]  (peer 는 *:* 라 제외)
    // netstat:   tcp 0 0 LOCAL PEER ESTABLISHED / ... 0.0.0.0:7000 0.0.0.0:* LISTEN
    // 첫번째=Local, (2개 이상이면) 마지막=Peer.
    private static List<String> addrsOf(String line) {
        String[] toks = line.trim().split("\\s+");
        List<String> addrs = new ArrayList<String>();
        for (String t : toks) if (isAddrPort(t)) addrs.add(t);
        return addrs;
    }

    // 유효한 주소:포트 토큰인가? (포트가 숫자여야 함 -> LISTEN 의 *:* / 0.0.0.0:* 는 제외)
    // 호스트: IPv4/IPv6(브래킷/콜론)/'*'(any) 허용.
    private static boolean isAddrPort(String t) {
        return t.matches("^(\\*|\\[?[0-9A-Fa-f:.%]+\\]?):[0-9]+$");
    }

    private static String portOf(String addrPort) {
        int i = addrPort.lastIndexOf(':');
        return i < 0 ? "" : addrPort.substring(i + 1);
    }

    private static String hostOf(String addrPort) {
        int i = addrPort.lastIndexOf(':');
        String h = i < 0 ? addrPort : addrPort.substring(0, i);
        if (h.startsWith("[") && h.endsWith("]")) h = h.substring(1, h.length() - 1);
        return h;
    }

    /** peer 가 지정 ip:port 와 일치? (IPv4-mapped ::ffff:x.x.x.x 도 허용) */
    private static boolean addrMatches(String peer, String ip, String port) {
        if (!port.equals(portOf(peer))) return false;
        String h = hostOf(peer);
        return h.equals(ip) || h.endsWith(":" + ip);
    }

    private static String rootMsg(Throwable e) {
        Throwable t = e;
        while (t.getCause() != null && t.getCause() != t) t = t.getCause();
        String m = t.getMessage();
        return (m == null ? t.getClass().getSimpleName() : t.getClass().getSimpleName() + ": " + m);
    }

    private static void closeAll(AutoCloseable... cs) {
        for (AutoCloseable c : cs) if (c != null) try { c.close(); } catch (Exception ignore) {}
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> asMap(Object o) {
        return o instanceof Map ? (Map<String, Object>) o : new LinkedHashMap<String, Object>();
    }

    @SuppressWarnings("unchecked")
    private static List<Object> asList(Object o) {
        return o instanceof List ? (List<Object>) o : new ArrayList<Object>();
    }

    private static String str(Object o, String def) { return o == null ? def : String.valueOf(o); }

    private static double num(Object o, double def) {
        if (o instanceof Number) return ((Number) o).doubleValue();
        if (o instanceof String) try { return Double.parseDouble((String) o); } catch (Exception e) { return def; }
        return def;
    }

    /** JSON string literal (escaped, quoted) */
    private static String jstr(String s) {
        if (s == null) return "\"\"";
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < s.length(); i++) {
            char ch = s.charAt(i);
            switch (ch) {
                case '"': sb.append("\\\""); break;
                case '\\': sb.append("\\\\"); break;
                case '\n': sb.append("\\n"); break;
                case '\r': sb.append("\\r"); break;
                case '\t': sb.append("\\t"); break;
                default:
                    if (ch < 0x20) sb.append(String.format("\\u%04x", (int) ch));
                    else sb.append(ch);
            }
        }
        return sb.append('"').toString();
    }

    private static final String FALLBACK_HTML =
            "<!doctype html><meta charset='utf-8'><h2>web/index.html 이 없습니다</h2>"
            + "<p>config.json 옆의 <code>web/index.html</code> 을 확인하세요.</p>";

    // =====================================================================
    // 최소 JSON 파서 (config.json 용) - 외부 의존성 없음
    // =====================================================================
    static final class Json {
        private final String s; private int i;
        private Json(String s) { this.s = s; }
        static Object parse(String s) { Json j = new Json(s); j.ws(); Object v = j.value(); j.ws(); return v; }

        private Object value() {
            char c = peek();
            switch (c) {
                case '{': return obj();
                case '[': return arr();
                case '"': return string();
                case 't': case 'f': return bool();
                case 'n': expect("null"); return null;
                default: return number();
            }
        }
        private Map<String, Object> obj() {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            expect('{'); ws();
            if (peek() == '}') { i++; return m; }
            while (true) {
                ws(); String k = string(); ws(); expect(':'); ws();
                m.put(k, value()); ws();
                char c = next();
                if (c == ',') continue;
                if (c == '}') break;
                throw err("expected , or }");
            }
            return m;
        }
        private List<Object> arr() {
            List<Object> a = new ArrayList<Object>();
            expect('['); ws();
            if (peek() == ']') { i++; return a; }
            while (true) {
                ws(); a.add(value()); ws();
                char c = next();
                if (c == ',') continue;
                if (c == ']') break;
                throw err("expected , or ]");
            }
            return a;
        }
        private String string() {
            expect('"');
            StringBuilder sb = new StringBuilder();
            while (true) {
                char c = s.charAt(i++);
                if (c == '"') break;
                if (c == '\\') {
                    char e = s.charAt(i++);
                    switch (e) {
                        case '"': sb.append('"'); break;
                        case '\\': sb.append('\\'); break;
                        case '/': sb.append('/'); break;
                        case 'n': sb.append('\n'); break;
                        case 'r': sb.append('\r'); break;
                        case 't': sb.append('\t'); break;
                        case 'b': sb.append('\b'); break;
                        case 'f': sb.append('\f'); break;
                        case 'u': sb.append((char) Integer.parseInt(s.substring(i, i + 4), 16)); i += 4; break;
                        default: sb.append(e);
                    }
                } else sb.append(c);
            }
            return sb.toString();
        }
        private Object number() {
            int start = i;
            while (i < s.length() && "+-0123456789.eE".indexOf(s.charAt(i)) >= 0) i++;
            return Double.parseDouble(s.substring(start, i));
        }
        private Boolean bool() {
            if (peek() == 't') { expect("true"); return Boolean.TRUE; }
            expect("false"); return Boolean.FALSE;
        }
        private void expect(char c) { if (next() != c) throw err("expected " + c); }
        private void expect(String w) {
            for (int k = 0; k < w.length(); k++) if (s.charAt(i++) != w.charAt(k)) throw err("expected " + w);
        }
        private char peek() { return s.charAt(i); }
        private char next() { return s.charAt(i++); }
        private void ws() { while (i < s.length() && Character.isWhitespace(s.charAt(i))) i++; }
        private RuntimeException err(String m) { return new RuntimeException("JSON parse error at " + i + ": " + m); }
    }
}
