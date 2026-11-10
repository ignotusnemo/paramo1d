package org.parano1d.courier;

import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Intent;
import android.graphics.Color;
import android.net.Uri;
import android.os.Bundle;
import android.webkit.JavascriptInterface;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import androidx.webkit.WebViewAssetLoader;
import org.json.JSONArray;
import org.json.JSONObject;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.security.SecureRandom;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public final class MainActivity extends Activity {
    private static java.lang.ref.WeakReference<MainActivity> active = new java.lang.ref.WeakReference<>(null);
    private WebView web;
    private AppLock appLock;
    private android.widget.FrameLayout root;
    private android.view.View lockScreen;
    private boolean lockScreenHasCredential;
    private boolean lockScreenDark;
    private boolean interfaceLoaded;
    private boolean pageReady;
    private boolean backupPickerActive;
    private boolean entryPromptAttempted;
    private final Set<Integer> unlockedSystemFlows = new HashSet<>();
    private static SecureStore store;
    private static android.content.Context application;
    private static JSONObject data;
    private String pendingBackup;
    private String pendingRestorePassword;
    private boolean notificationPermissionAsked;
    private static final String ORIGIN = "https://appassets.androidplatform.net";
    private static final ExecutorService chatWorker = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(32));
    private static final ExecutorService chainWorker = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(2));
    private static final ExecutorService deliveryWorker = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(2));
    private static final ExecutorService inboxWorker = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(1));
    private static final ExecutorService paymentDeliveryWorker = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(2));
    private static final Set<String> sendingPayments = new HashSet<>();
    private static boolean deliveryBusy;
    private static boolean inboxBusy;
    private static long nextInboxAttempt;
    private static long connectionGeneration;
    private static volatile boolean visible;
    private static String activeConversation = "";
    private static boolean paymentFlow;
    private static boolean walletVisible;
    private static long nextNodeAttempt;
    private static PendingChain pendingChain;
    private final android.os.Handler nodeTimer = new android.os.Handler(android.os.Looper.getMainLooper());
    private final android.content.BroadcastReceiver screenOff = new android.content.BroadcastReceiver() {
        @Override public void onReceive(android.content.Context context, Intent intent) { pauseNode(); }
    };
    private static final class PendingChain {
        final MainActivity owner; final String id; final JSONObject request;
        PendingChain(MainActivity owner,String id,JSONObject request) { this.owner=owner;this.id=id;this.request=request; }
    }
    private final Runnable nodeTick = new Runnable() {
        @Override public void run() {
            if (!nodeAllowed()) { pauseNode(); return; }
            try { chatWorker.execute(() -> { try {
                if (data==null || !data.has("seed_hex") || data.getJSONObject("chain").optBoolean("running") || pendingChain!=null || paymentFlow || System.currentTimeMillis()<nextNodeAttempt || !nodeAllowed() || data.getJSONObject("settings").optString("rpc").isEmpty()) return;
                if(!data.getJSONObject("chain").has("height") && !walletVisible) return;
                if (data.optBoolean("protected_route") && !protectedRoute) return;
                startChainAction(null,new JSONObject().put("op","sync"),true);
            } catch(Exception ignored) {} }); } catch(RuntimeException ignored) {}
            nodeTimer.postDelayed(this,3000);
        }
    };
    private static final android.os.Handler deliveryTimer = new android.os.Handler(android.os.Looper.getMainLooper());
    private static volatile boolean protectedRoute;
    private static boolean tunnelStarting;
    private static long nextProtectionAttempt;
    private static int protectionFailures;
    private static JSONObject tunnelState = new JSONObject();
    private static final Set<String> CHAIN_ACTIONS = new HashSet<>(java.util.Arrays.asList("sync", "payment_preview", "payment_send", "receipt_verify", "broadcast_preview", "broadcast_send"));

    @Override public void onCreate(Bundle bundle) {
        super.onCreate(bundle);
        active = new java.lang.ref.WeakReference<>(this);
        application = getApplicationContext();
        appLock = new AppLock(this);
        applySystemTheme(getSharedPreferences("interface",MODE_PRIVATE).getString("theme","system"));
        if (!BuildConfig.DEBUG) getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_SECURE);
        if (store == null) store = new SecureStore(getApplicationContext());
        web = new WebView(this);
        WebSettings settings = web.getSettings(); settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(false); settings.setAllowFileAccess(false); settings.setAllowContentAccess(false);
        settings.setMixedContentMode(WebSettings.MIXED_CONTENT_NEVER_ALLOW);
        settings.setSupportMultipleWindows(false); settings.setJavaScriptCanOpenWindowsAutomatically(false);
        WebView.setWebContentsDebuggingEnabled(BuildConfig.DEBUG);
        WebViewAssetLoader loader = new WebViewAssetLoader.Builder().addPathHandler("/assets/", new WebViewAssetLoader.AssetsPathHandler(this)).build();
        web.setWebViewClient(new WebViewClient() {
            @Override public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                if (request.getUrl().getHost() != null && request.getUrl().getHost().equals("appassets.androidplatform.net")) return loader.shouldInterceptRequest(request.getUrl());
                return new WebResourceResponse("text/plain", "utf-8", 403, "External resources blocked", java.util.Collections.emptyMap(), new java.io.ByteArrayInputStream(new byte[0]));
            }
            @Override public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) { return !request.getUrl().toString().startsWith(ORIGIN + "/assets/"); }
            @Override public void onPageFinished(WebView view, String url) { pageReady = true; handleContactIntent(getIntent()); }
        });
        web.addJavascriptInterface(new Bridge(), "Paramo1d");
        root = new android.widget.FrameLayout(this);
        root.addView(web, new android.widget.FrameLayout.LayoutParams(-1, -1));
        if (android.os.Build.VERSION.SDK_INT >= 35) root.setOnApplyWindowInsetsListener((view, insets) -> {
            android.graphics.Insets bars = insets.getInsets(android.view.WindowInsets.Type.systemBars() | android.view.WindowInsets.Type.displayCutout());
            android.graphics.Insets keyboard = insets.getInsets(android.view.WindowInsets.Type.ime());
            view.setPadding(bars.left, bars.top, bars.right, Math.max(bars.bottom, keyboard.bottom)); return insets;
        });
        setContentView(root);
        applySystemTheme(getSharedPreferences("interface",MODE_PRIVATE).getString("theme","system"));
        android.content.IntentFilter screenFilter=new android.content.IntentFilter(Intent.ACTION_SCREEN_OFF);
        if (android.os.Build.VERSION.SDK_INT>=33) registerReceiver(screenOff,screenFilter,RECEIVER_NOT_EXPORTED); else registerReceiver(screenOff,screenFilter);
        if (appLock.needsUnlock()) showLockScreen(); else openInterface();
    }

    @Override protected void onNewIntent(Intent intent) { super.onNewIntent(intent); setIntent(intent); handleContactIntent(intent); }
    @Override public void startActivityForResult(Intent intent, int request) {
        if ((request == 62 || request == 63) && appLock != null && !appLock.needsUnlock()) unlockedSystemFlows.add(request);
        super.startActivityForResult(intent, request);
    }
    @Override protected void onResume() {
        super.onResume(); visible = true;
        if (appLock != null && !appLock.authenticating()) {
            if (appLock.needsUnlock()) { showLockScreen(); if (!entryPromptAttempted) { entryPromptAttempted = true; appLock.authenticate(this::openInterface, () -> {}); } }
            else openInterface();
        }
        deliveryPoll();
    }
    @Override protected void onPause() {
        visible = false;
        pauseNode();
        if (appLock != null) { if (!appLock.authenticating()) entryPromptAttempted = false; appLock.backgrounded(); if (AppLock.enabled(this) && new File(getFilesDir(), "identity.pmc").isFile()) showLockScreen(); }
        super.onPause();
    }
    private void openInterface() {
        appLock.opened();
        entryPromptAttempted = false;
        if (lockScreen != null) lockScreen.setVisibility(android.view.View.GONE);
        web.setVisibility(android.view.View.VISIBLE);
        if (BuildConfig.DEBUG) getWindow().clearFlags(android.view.WindowManager.LayoutParams.FLAG_SECURE);
        if (!interfaceLoaded) { interfaceLoaded = true; web.loadUrl(ORIGIN + "/assets/index.html"); }
        else { if (pageReady) handleContactIntent(getIntent()); chatWorker.execute(() -> { try { if (data != null) publishView(); } catch (Exception ignored) {} }); }
        if (visible) { nextNodeAttempt=0;nodeControl(true); nodeTimer.removeCallbacks(nodeTick); nodeTimer.postDelayed(nodeTick,1000); }
    }
    private boolean nodeAllowed() {
        return visible && appLock!=null && !appLock.needsUnlock() && !getSystemService(android.app.KeyguardManager.class).isDeviceLocked() && getSystemService(android.os.PowerManager.class).isInteractive();
    }
    private static void nodeControl(boolean active) {
        try { NativeCore.call(new JSONObject().put("op","node_active").put("active",active).toString()); } catch(Throwable ignored) {}
    }
    private void pauseNode() { nodeTimer.removeCallbacks(nodeTick); nodeControl(false); walletScreenAwake(false); if(BuildConfig.DEBUG) android.util.Log.d("Paramo1dNode","Paused"); }
    private void showLockScreen() {
        if (root == null) return;
        web.setVisibility(android.view.View.INVISIBLE);
        getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_SECURE);
        boolean secure = AppLock.available(this);
        String theme = getSharedPreferences("interface", MODE_PRIVATE).getString("theme", "system");
        boolean dark = theme.equals("dark") || theme.equals("system") && (getResources().getConfiguration().uiMode & android.content.res.Configuration.UI_MODE_NIGHT_MASK) == android.content.res.Configuration.UI_MODE_NIGHT_YES;
        if (lockScreen != null && (secure != lockScreenHasCredential || dark != lockScreenDark)) { root.removeView(lockScreen); lockScreen = null; }
        if (lockScreen == null) {
            lockScreenHasCredential = secure; lockScreenDark = dark;
            int ink = dark ? Color.rgb(238,246,239) : Color.rgb(7,18,13);
            android.widget.LinearLayout panel = new android.widget.LinearLayout(this); panel.setOrientation(android.widget.LinearLayout.VERTICAL); panel.setGravity(android.view.Gravity.CENTER); int padding = (int)(28 * getResources().getDisplayMetrics().density); panel.setPadding(padding,padding,padding,padding); panel.setBackgroundColor(dark ? Color.rgb(16,20,19) : Color.rgb(246,246,238));
            android.widget.ImageView logo = new android.widget.ImageView(this); logo.setImageResource(R.mipmap.ic_launcher); int logoSize = (int)(72 * getResources().getDisplayMetrics().density); android.widget.LinearLayout.LayoutParams logoLayout = new android.widget.LinearLayout.LayoutParams(logoSize,logoSize); logoLayout.bottomMargin = padding; panel.addView(logo,logoLayout);
            android.widget.TextView title = new android.widget.TextView(this); title.setText("Paramo1d"); title.setTypeface(android.graphics.Typeface.MONOSPACE, android.graphics.Typeface.BOLD); title.setTextSize(30); title.setTextColor(ink); panel.addView(title);
            android.widget.TextView explanation = new android.widget.TextView(this); explanation.setText("Unlock to open your messages and wallet.\nUse your fingerprint or phone PIN."); explanation.setTextSize(16); explanation.setTextColor(ink); explanation.setGravity(android.view.Gravity.CENTER); explanation.setPadding(0,padding,0,padding); panel.addView(explanation);
            android.widget.Button unlock = new android.widget.Button(this); unlock.setText("Unlock Paramo1d"); unlock.setAllCaps(false); unlock.setTextColor(Color.rgb(7,18,13)); unlock.setBackgroundTintList(android.content.res.ColorStateList.valueOf(Color.rgb(0,255,128))); unlock.setOnClickListener(v -> appLock.authenticate(this::openInterface, () -> {})); panel.addView(unlock);
            if (!AppLock.available(this)) { unlock.setEnabled(false); android.widget.Button setup = new android.widget.Button(this); setup.setText("Set up phone screen lock"); setup.setAllCaps(false); setup.setOnClickListener(v -> startActivity(new Intent(android.provider.Settings.ACTION_SECURITY_SETTINGS))); panel.addView(setup); }
            lockScreen = panel; root.addView(panel, new android.widget.FrameLayout.LayoutParams(-1,-1));
        }
        lockScreen.setVisibility(android.view.View.VISIBLE);
    }
    private void handleContactIntent(Intent intent) {
        if (appLock.needsUnlock() || !pageReady) return;
        String destination = intent.getStringExtra("open_chat");
        if (destination != null && destination.matches("d:[0-9a-f]{64}")) { web.evaluateJavascript("window.paramo1dOpenChat(" + JSONObject.quote(destination) + ")", null); intent.removeExtra("open_chat"); }
        Uri uri = intent.getData();
        if (uri != null && "paramo1d".equals(uri.getScheme()) && "contact".equals(uri.getHost())) {
            web.evaluateJavascript("window.paramo1dOpenContact(" + JSONObject.quote(uri.toString()) + ")", null); intent.setData(null);
        }
    }
    private void reply(String id, JSONObject response) {
        if (id==null) return;
        final String script = "window.paramo1dReply(" + JSONObject.quote(id) + "," + response.toString() + ")";
        runOnUiThread(() -> { if (!isFinishing() && !isDestroyed()) web.evaluateJavascript(script, null); });
    }
    private JSONObject success(Object result) { try { return new JSONObject().put("ok", true).put("result", result); } catch (org.json.JSONException impossible) { throw new IllegalStateException(impossible); } }
    private JSONObject failure(Exception error) { try { return new JSONObject().put("ok", false).put("error", error.getMessage() == null ? "Operation failed" : error.getMessage()); } catch (org.json.JSONException impossible) { throw new IllegalStateException(impossible); } }
    private final class Bridge {
        @JavascriptInterface public void request(String id, String encoded) {
            if (id.length() > 32 || encoded.length() > 2 * 1024 * 1024) { reply(id, failure(new Exception("Request exceeds limit"))); return; }
            try { chatWorker.execute(() -> {
                try {
                    if (appLock.needsUnlock()) { runOnUiThread(MainActivity.this::showLockScreen); throw new Exception("Unlock Paramo1d to continue."); }
                    if (data == null) { data = store.read(); initializeFields(); }
                    JSONObject request = new JSONObject(encoded); String op = request.getString("op");
                    if (CHAIN_ACTIONS.contains(op)) { startChainAction(id, request); return; }
                    reply(id, success(handle(request)));
                } catch (Exception error) { reply(id, failure(error)); }
            }); } catch (Exception busy) { reply(id, failure(new Exception("Please wait for the current operation"))); }
        }
    }

    private static void initializeFields() throws Exception {
        for (String key : new String[]{"contacts", "messages", "receipts", "outbox", "observations", "watches", "prepared_payments", "envelopes"}) if (!data.has(key)) data.put(key, new JSONArray());
        if (!data.has("settings")) data.put("settings", new JSONObject().put("relays", new JSONArray().put("https://chat.parano1d.org")).put("rpc", "https://chat.parano1d.org/chain"));
        if (!data.has("cursors")) data.put("cursors", new JSONObject());
        if (!data.has("read_messages")) data.put("read_messages", new JSONObject());
        if (!data.has("chain")) data.put("chain", new JSONObject());
        if (!data.has("background_delivery")) data.put("background_delivery",true);
        data.put("connection", new JSONObject().put("online", false));
        data.getJSONObject("chain").put("running", false);
        if (data.has("seed_hex") && (data.optBoolean("background_delivery") || data.optBoolean("protected_route")) && !DeliveryService.isRunning()) {
            try { application.startForegroundService(new Intent(application, DeliveryService.class)); } catch (RuntimeException requiresForeground) { }
        }
        if (data.optBoolean("protected_route") && !protectedRoute) beginProtection();
        if (!data.has("next_address")) data.put("next_address", 1);
    }
    private static void ensureDefaultDelivery() {
        if (data==null || !data.has("seed_hex") || !(data.optBoolean("background_delivery",true) || data.optBoolean("protected_route")) || DeliveryService.isRunning()) return;
        try { application.startForegroundService(new Intent(application,DeliveryService.class)); } catch(RuntimeException requiresForeground) {}
    }
    private static JSONObject view() throws Exception {
        JSONObject result = new JSONObject();
        for (String key : new String[]{"profile", "invite", "contacts", "messages", "receipts", "settings", "chain", "connection", "observations"}) if (data.has(key)) result.put(key, data.get(key));
        JSONArray pending = new JSONArray(), packets = data.getJSONArray("prepared_payments");
        for (int i = 0; i < packets.length(); i++) { JSONObject packet = packets.getJSONObject(i), entry = new JSONObject(); for (String key : new String[]{"txid", "to", "amount", "fee", "submitted", "created_ms", "delivery_error"}) if (packet.has(key)) entry.put(key, packet.get(key)); pending.put(entry); }
        result.put("prepared_payments", pending);
        result.put("nearby", NearbyService.snapshot());
        result.put("protection", tunnelState);
        result.put("background_delivery", data.optBoolean("background_delivery",true) || data.optBoolean("protected_route"));
        result.put("delivery_running", DeliveryService.isRunning());
        if(data.has("seed_hex")) result.put("node",nativeResult(new JSONObject().put("op","node_status")));
        result.put("security", AppLock.state(application));
        result.put("backup_saved", data.optLong("backup_saved_ms") > 0);
        result.put("storage_full", data.optBoolean("storage_full"));
        result.put("notifications_enabled", application.getSystemService(android.app.NotificationManager.class).areNotificationsEnabled());
        JSONObject unread = new JSONObject(), read = data.getJSONObject("read_messages"); JSONArray history = data.getJSONArray("messages"); String own = data.optJSONObject("profile") == null ? "" : data.getJSONObject("profile").getString("id");
        for (int i = 0; i < history.length(); i++) { JSONObject message = history.getJSONObject(i); String scope = message.getString("chat"); if (message.getString("id").equals(read.optString(scope))) unread.put(scope,0); else if (!message.getJSONObject("sender").getString("id").equals(own)) unread.put(scope, unread.optInt(scope) + 1); }
        result.put("unread", unread);
        result.put("connection", new JSONObject(data.optJSONObject("connection").toString()).put("checking", inboxBusy && !data.getJSONObject("connection").optBoolean("online")));
        return result.put("rooms", new JSONArray().put("parano1d"));
    }
    private static void requireIdentity() throws Exception { if (!data.has("seed_hex")) throw new Exception("Create or restore your identity first"); }
    private static JSONObject core(String op, JSONObject args) throws Exception {
        args.put("op", op);
        if (data.has("seed_hex")) args.put("seed_hex", data.getString("seed_hex"));
        args.put("now_ms", System.currentTimeMillis());
        return nativeResult(args);
    }
    private static JSONObject nativeResult(JSONObject args) throws Exception {
        JSONObject result = new JSONObject(NativeCore.call(args.toString()));
        if (!result.optBoolean("ok")) throw new Exception(result.optString("error", "Native operation failed"));
        return result.getJSONObject("result");
    }
    private static String randomHex(int count) { byte[] bytes = new byte[count]; new SecureRandom().nextBytes(bytes); StringBuilder s = new StringBuilder(); for (byte b : bytes) s.append(String.format(java.util.Locale.ROOT, "%02x", b & 255)); return s.toString(); }

    private Object handle(JSONObject request) throws Exception {
        String op = request.getString("op");
        if (op.equals("boot")) { runOnUiThread(() -> applySystemTheme(data.optJSONObject("settings").optString("theme", "system"))); if(data.has("seed_hex")) { ensureDefaultDelivery(); if(data.optBoolean("background_delivery",true) || data.optBoolean("protected_route")) askNotificationPermission(); } return view(); }
        if (op.equals("create_identity")) {
            if (data.has("seed_hex")) throw new Exception("An identity already exists");
            String name = request.getString("name").trim(); if (name.isEmpty() || name.length() > 40) throw new Exception("Enter a display name");
            data.put("seed_hex", randomHex(32)); JSONObject profile = core("profile", new JSONObject().put("name", name));
            data.put("profile", profile.getJSONObject("contact")).put("invite", profile.getString("invite")); store.save(data); ensureDefaultDelivery(); askNotificationPermission(); return view();
        }
        if (op.equals("backup_restore")) {
            if (data.has("seed_hex")) throw new Exception("Restore on an empty installation to preserve your current identity");
            JSONObject result = nativeResult(new JSONObject(request.toString()).put("op", "backup_decrypt"));
            JSONObject restored = result.getJSONObject("data");
            JSONObject profile = nativeResult(new JSONObject().put("op", "profile").put("seed_hex", restored.getString("seed_hex")).put("name", restored.getJSONObject("profile").getString("name")));
            if (!profile.getJSONObject("contact").getString("id").equals(restored.getJSONObject("profile").getString("id"))) throw new Exception("Backup identity does not match");
            restored.remove("tunnel_config"); restored.put("protected_route", false);
            data = restored; initializeFields(); store.save(data); ensureDefaultDelivery(); askNotificationPermission(); return view();
        }
        if (op.equals("backup_restore_file")) {
            if (data.has("seed_hex")) throw new Exception("Restore on an empty installation");
            pendingRestorePassword = request.getString("password");
            if (pendingRestorePassword.length() < 12) throw new Exception("Enter the backup password");
            runOnUiThread(() -> { backupPickerActive = true; startActivityForResult(new Intent(Intent.ACTION_OPEN_DOCUMENT).addCategory(Intent.CATEGORY_OPENABLE).setType("application/json"), 41); });
            return new JSONObject().put("selecting", true);
        }
        requireIdentity();
        switch (op) {
            case "app_lock": AppLock.setEnabled(this, request.getBoolean("enabled")); return view();
            case "lock_now": appLock.lock(); pauseNode(); runOnUiThread(this::showLockScreen); return new JSONObject().put("locked", true);
            case "phone_security": runOnUiThread(() -> startActivity(new Intent(android.provider.Settings.ACTION_SECURITY_SETTINGS))); return new JSONObject().put("opening", true);
            case "notification_settings": runOnUiThread(() -> startActivity(new Intent(android.provider.Settings.ACTION_APP_NOTIFICATION_SETTINGS).putExtra(android.provider.Settings.EXTRA_APP_PACKAGE,getPackageName()))); return new JSONObject().put("opening", true);
            case "clear_history": {
                if (!request.optBoolean("confirmed")) throw new Exception("Confirm clearing local chat history.");
                Set<String> queued = new HashSet<>(); JSONArray outbox = data.getJSONArray("outbox");
                for (int i = 0; i < outbox.length(); i++) queued.add(outbox.getJSONObject(i).getString("id"));
                JSONArray kept = new JSONArray(), messages = data.getJSONArray("messages"), receipts = data.getJSONArray("receipts"), observations = data.getJSONArray("observations"), prepared = data.getJSONArray("prepared_payments"), pending = new JSONArray();
                for (int i = 0; i < messages.length(); i++) if (queued.contains(messages.getJSONObject(i).getString("id"))) kept.put(messages.getJSONObject(i));
                Set<String> checked = new HashSet<>();
                for (int i = 0; i < receipts.length(); i++) { JSONObject receipt = receipts.getJSONObject(i); if (!receipt.optBoolean("verified")) continue; String txid = receipt.getString("txid"); checked.add(txid);
                    for (int j = 0; j < prepared.length(); j++) { JSONObject packet = prepared.getJSONObject(j); if (packet.getString("txid").equals(txid) && receipt.isNull("amount")) receipt.put("amount",packet.optString("amount")); }
                    if (receipt.optString("receipt_hex").isEmpty()) for (int j = 0; j < observations.length(); j++) { JSONObject observation = observations.getJSONObject(j), message = observation.getJSONObject("message"); if (observation.getJSONObject("sender").getString("id").equals(data.getJSONObject("profile").getString("id")) && message.optString("txid").equals(txid) && !message.isNull("receipt_hex")) { receipt.put("receipt_hex",message.optString("receipt_hex")); break; } }
                }
                Set<String> preserveReports = new HashSet<>();
                for (int i = 0; i < prepared.length(); i++) if (!checked.contains(prepared.getJSONObject(i).getString("txid"))) { pending.put(prepared.getJSONObject(i)); preserveReports.add(prepared.getJSONObject(i).getString("txid")); }
                for (int i = 0; i < receipts.length(); i++) if (receipts.getJSONObject(i).optString("receipt_hex").isEmpty()) preserveReports.add(receipts.getJSONObject(i).optString("txid"));
                JSONArray reports = new JSONArray(); for (int i = 0; i < observations.length(); i++) if (preserveReports.contains(observations.getJSONObject(i).getJSONObject("message").optString("txid"))) reports.put(observations.getJSONObject(i));
                data.put("messages",kept).put("envelopes",new JSONArray(outbox.toString())).put("observations",reports).put("prepared_payments",pending).put("read_messages",new JSONObject()).put("storage_full",false);
                store.save(data); nextInboxAttempt = 0; poll(); return view();
            }
            case "view_chat": {
                String scope = request.getString("chat");
                if (!scope.isEmpty() && !scope.equals("g:parano1d") && !scope.matches("d:[0-9a-f]{64}")) throw new Exception("Choose a conversation.");
                activeConversation = scope;
                paymentFlow=request.optBoolean("payment_flow");
                walletVisible=request.optBoolean("wallet_visible");
                return new JSONObject().put("updated",true);
            }
            case "mark_read": {
                String scope = request.getString("chat"), marker = request.getString("message_id"); JSONArray messages = data.getJSONArray("messages"); boolean found = false;
                if (!visible) return view();
                if (!scope.equals("g:parano1d") && !scope.matches("d:[0-9a-f]{64}")) throw new Exception("Choose a conversation.");
                for (int i = 0; i < messages.length(); i++) if (messages.getJSONObject(i).getString("id").equals(marker) && messages.getJSONObject(i).getString("chat").equals(scope)) { found = true; break; }
                if (found && !data.getJSONObject("read_messages").optString(scope).equals(marker)) { data.getJSONObject("read_messages").put(scope,marker); store.save(data); }
                if (found) getSystemService(android.app.NotificationManager.class).cancel(1000 + Math.floorMod(scope.hashCode(),1000000));
                return view();
            }
            case "settings": {
                JSONArray relays = request.getJSONArray("relays"); if (relays.length() > 3) throw new Exception("Use up to three delivery relays");
                JSONArray checked = new JSONArray(); for (int i = 0; i < relays.length(); i++) checked.put(checkEndpoint(relays.getString(i)));
                String rpc = request.optString("rpc").trim(); if (!rpc.isEmpty()) checkEndpoint(rpc);
                data.put("settings", new JSONObject().put("relays", checked).put("rpc", rpc).put("theme", data.getJSONObject("settings").optString("theme", "system"))); connectionGeneration++; data.put("connection", new JSONObject().put("online", false)); nextInboxAttempt = 0; directClient.dispatcher().cancelAll(); store.save(data); poll(); return view();
            }
            case "join_group": if (!request.getString("room").equals("parano1d")) throw new Exception("This version uses the community chat"); return view();
            case "import_contact": return addContact(core("contact_import", new JSONObject().put("uri", request.getString("uri"))).getJSONObject("contact"));
            case "add_contact": return addContact(request.getJSONObject("contact"));
            case "send": sendMessage(request.getString("chat"), request.getJSONObject("message")); flushOutbox(); store.save(data); return view();
            case "invoice": {
                core("amount", new JSONObject().put("amount", request.getString("amount")));
                String address = data.getJSONObject("profile").getString("address");
                JSONObject invoice = new JSONObject().put("type", "invoice").put("invoice_id", randomHex(16)).put("address", address).put("amount", request.getString("amount")).put("memo", request.optString("memo"));
                sendMessage("d:" + request.getString("contact_id"), invoice); flushOutbox(); store.save(data); return view();
            }
            case "poll": poll(); return view();
            case "theme": {
                String theme = request.getString("value");
                if (!theme.equals("light") && !theme.equals("dark") && !theme.equals("system")) throw new Exception("Choose a display theme");
                data.getJSONObject("settings").put("theme", theme); getSharedPreferences("interface", MODE_PRIVATE).edit().putString("theme", theme).apply(); store.save(data); runOnUiThread(() -> applySystemTheme(theme)); return view();
            }
            case "background_enable":
                askNotificationPermission();
                application.startForegroundService(new Intent(application, DeliveryService.class)); data.put("background_delivery", true); store.save(data); return view();
            case "background_disable":
                stopDelivery(); application.stopService(new Intent(application, DeliveryService.class)); return view();
            case "protection_enable":
                if(data.getJSONObject("chain").optBoolean("running") && !data.getJSONObject("chain").optBoolean("automatic")) throw new Exception("Wait for the current wallet operation");
                nodeControl(false);
                askNotificationPermission();
                if (request.has("prefer_https")) {
                    if (!data.has("tunnel_config")) data.put("tunnel_config", tunnelCore(new JSONObject().put("op", "keypair")));
                    data.getJSONObject("tunnel_config").put("prefer_https", request.getBoolean("prefer_https"));
                }
                application.startForegroundService(new Intent(application, DeliveryService.class));
                data.put("background_delivery", true); beginProtection(); return view();
            case "protection_disable":
                if (data.getJSONObject("chain").optBoolean("running") && !data.getJSONObject("chain").optBoolean("automatic")) throw new Exception("Wait for the current wallet operation");
                nodeControl(false);
                data.put("protected_route", false); store.save(data); protectedRoute = false;
                connectionGeneration++; data.put("connection", new JSONObject().put("online", false)); nextInboxAttempt = 0;
                core("route_set", new JSONObject()); tunnelCore(new JSONObject().put("op", "stop"));
                tunnelState = new JSONObject().put("enabled", false); poll(); return view();
            case "nearby_start": runOnUiThread(this::startNearby); return view();
            case "nearby_stop": runOnUiThread(() -> stopService(new Intent(this, NearbyService.class))); return view();
            case "nearby_scan": NearbyService.scan(); return view();
            case "nearby_connect": NearbyService.connect(request.getString("address")); return view();
            case "nearby_visible": runOnUiThread(() -> startActivityForResult(new Intent(android.bluetooth.BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE).putExtra(android.bluetooth.BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, 120), 63)); return view();
            case "share_prepared": {
                JSONArray packets = data.getJSONArray("prepared_payments");
                for (int i = 0; i < packets.length(); i++) if (packets.getJSONObject(i).getString("txid").equals(request.getString("txid"))) {
                    String destination = request.optString("chat", "g:parano1d");
                    if (!destination.equals("g:parano1d") && !destination.startsWith("d:")) throw new Exception("Choose the community or a contact");
                    sendMessage(destination, new JSONObject().put("type", "transaction").put("intent_hex", packets.getJSONObject(i).getString("intent_hex"))); watch(request.getString("txid"), destination); flushOutbox(); store.save(data); return view();
                }
                throw new Exception("Authorized payment is unavailable");
            }
            case "retry_payment": {
                JSONArray packets = data.getJSONArray("prepared_payments");
                for (int i = 0; i < packets.length(); i++) if (packets.getJSONObject(i).getString("txid").equals(request.getString("txid"))) { queueOwnBroadcast(packets.getJSONObject(i)); return view(); }
                throw new Exception("Saved payment is unavailable.");
            }
            case "share_receipt": {
                String txid = request.getString("txid"), encoded = ""; boolean verified = false;
                JSONArray receipts = data.getJSONArray("receipts");
                for (int i = 0; i < receipts.length(); i++) { JSONObject receipt = receipts.getJSONObject(i); if (receipt.optBoolean("verified") && receipt.optString("txid").equals(txid)) { verified = true; encoded = receipt.optString("receipt_hex"); break; } }
                if (!verified) throw new Exception("Check this payment before sharing its receipt.");
                if (encoded.isEmpty()) { JSONArray observations = data.getJSONArray("observations"); for (int i = 0; i < observations.length(); i++) { JSONObject message = observations.getJSONObject(i).getJSONObject("message"); if (message.optString("txid").equals(txid) && !message.optString("receipt_hex").isEmpty() && !message.isNull("receipt_hex")) { encoded = message.getString("receipt_hex"); break; } } }
                if (encoded.isEmpty()) throw new Exception("Receipt data is unavailable. Check the payment again.");
                sendMessage(request.getString("chat"), new JSONObject().put("type", "receipt").put("invoice_id", request.getString("invoice_id")).put("receipt_hex", encoded)); flushOutbox(); return view();
            }
            case "copy": {
                String text = request.getString("text"); runOnUiThread(() -> ((ClipboardManager) getSystemService(CLIPBOARD_SERVICE)).setPrimaryClip(ClipData.newPlainText("Paramo1d", text))); return new JSONObject().put("copied", true);
            }
            case "share": {
                String text = request.getString("text"); runOnUiThread(() -> startActivity(Intent.createChooser(new Intent(Intent.ACTION_SEND).setType("text/plain").putExtra(Intent.EXTRA_TEXT, text), "Share contact"))); return new JSONObject().put("shared", true);
            }
            case "backup_export": {
                pendingBackup = core("backup_encrypt", new JSONObject().put("data", data.toString()).put("password", request.getString("password"))).getString("backup");
                runOnUiThread(() -> { backupPickerActive = true; startActivityForResult(new Intent(Intent.ACTION_CREATE_DOCUMENT).addCategory(Intent.CATEGORY_OPENABLE).setType("application/json").putExtra(Intent.EXTRA_TITLE, "paramo1d-backup.json"), 40); });
                return new JSONObject().put("exporting", true);
            }
            default: throw new Exception("Unknown application action");
        }
    }

    private static JSONObject findContact(String id) throws Exception {
        JSONArray contacts = data.getJSONArray("contacts"); for (int i = 0; i < contacts.length(); i++) if (contacts.getJSONObject(i).getString("id").equals(id)) return contacts.getJSONObject(i);
        throw new Exception("Add this contact first");
    }
    private static JSONObject addContact(JSONObject contact) throws Exception {
        String id = contact.getString("id"); if (!id.matches("[0-9a-f]{64}")) throw new Exception("Invalid contact identity");
        if (id.equals(data.getJSONObject("profile").getString("id"))) return view();
        JSONArray contacts = data.getJSONArray("contacts");
        for (int i = 0; i < contacts.length(); i++) if (contacts.getJSONObject(i).getString("id").equals(id)) {
            if (!contacts.getJSONObject(i).getString("box_key").equals(contact.getString("box_key"))) throw new Exception("This contact's encryption key has changed"); return view();
        }
        if (contacts.length() >= 1000) throw new Exception("Contact limit reached"); contacts.put(contact); store.save(data); return view();
    }
    private static void sendMessage(String chat, JSONObject message) throws Exception {
        if (data.getJSONArray("messages").length() >= 5000) throw new SecureStore.Full();
        JSONObject destination;
        if (chat.equals("g:parano1d")) destination = new JSONObject().put("type", "group").put("room", "parano1d");
        else if (chat.startsWith("d:")) destination = new JSONObject().put("type", "direct").put("contact", findContact(chat.substring(2)));
        else throw new Exception("Unknown conversation");
        JSONObject payment = message.optString("type").equals("transaction") ? core("broadcast_preview", new JSONObject().put("intent_hex", message.getString("intent_hex"))) : null;
        JSONObject envelope = core("seal", new JSONObject().put("sender", data.getJSONObject("profile")).put("destination", destination).put("message", message)).getJSONObject("envelope");
        int envelopeBytes = envelope.toString().getBytes(StandardCharsets.UTF_8).length;
        if (data.getJSONArray("outbox").toString().getBytes(StandardCharsets.UTF_8).length + envelopeBytes > 4 * 1024 * 1024) throw new Exception("Outgoing queue is full. Reconnect before sending more messages.");
        store.reserveRoom(Math.multiplyExact(4,envelopeBytes));
        JSONObject local = new JSONObject().put("id", envelope.getString("id")).put("chat", chat).put("sender", data.getJSONObject("profile")).put("message", message).put("created_ms", System.currentTimeMillis()).put("status", "queued");
        if (payment != null) local.put("payment", payment);
        if (!message.optString("type").equals("relay_update")) data.getJSONArray("messages").put(local);
        else recordObservation(local);
        data.getJSONArray("outbox").put(envelope); store.save(data);
        retainEnvelope(envelope); NearbyService.offer(envelope);
    }
    private static void flushOutbox() throws Exception {
        queueDelivery();
    }
    private static void poll() throws Exception {
        if (protectedRoute && !tunnelStarting && !tunnelState.optBoolean("connected") && System.currentTimeMillis() >= nextProtectionAttempt) beginProtection();
        queueDelivery();
        queueInbox();
        retryPendingPayments(false);
        scheduleObservations();
    }
    private static void queueDelivery() throws Exception {
        if (deliveryBusy || tunnelStarting) return;
        if (data.getJSONArray("outbox").length() == 0) return;
        JSONObject snapshot = new JSONObject();
        for (String key : new String[]{"settings", "cursors", "outbox", "profile", "seed_hex"}) snapshot.put(key, data.get(key));
        final JSONObject frozen = new JSONObject(snapshot.toString()); deliveryBusy = true;
        deliveryWorker.execute(() -> {
            Set<String> delivered = new HashSet<>(), expired = new HashSet<>();
            try {
                JSONArray relays = frozen.getJSONObject("settings").getJSONArray("relays"); JSONArray outbox = frozen.getJSONArray("outbox");
                for (int j = 0; j < relays.length(); j++) {
                    String relay = relays.getString(j);
                    for (int i = 0; i < Math.min(outbox.length(), 8); i++) {
                        JSONObject envelope = outbox.getJSONObject(i);
                        if (envelope.getJSONObject("data").getLong("expires_ms") <= System.currentTimeMillis()) { expired.add(envelope.getString("id")); continue; }
                        try { http(relay, "/v1/messages", envelope, null); delivered.add(envelope.getString("id")); } catch (Exception unavailable) { if (BuildConfig.DEBUG) android.util.Log.d("Paramo1dConnection", unavailable.getClass().getSimpleName() + ": " + unavailable.getMessage()); break; }
                    }
                }
            } catch (Exception unavailable) { }
            chatWorker.execute(() -> { try {
                JSONArray remaining = new JSONArray(), outbox = data.getJSONArray("outbox");
                for (int i = 0; i < outbox.length(); i++) { JSONObject envelope = outbox.getJSONObject(i); if (!delivered.contains(envelope.getString("id")) && !expired.contains(envelope.getString("id"))) remaining.put(envelope); }
                data.put("outbox", remaining);
                JSONArray messages = data.getJSONArray("messages");
                for (int i = 0; i < messages.length(); i++) { JSONObject message = messages.getJSONObject(i); if (delivered.contains(message.getString("id"))) message.put("status", "sent"); if (expired.contains(message.getString("id"))) message.put("status", "expired"); }
                if (!delivered.isEmpty() || !expired.isEmpty()) store.save(data);
                publishView();
            } catch (Exception ignored) { } finally { deliveryBusy = false; if (!delivered.isEmpty() || !expired.isEmpty()) try { queueDelivery(); } catch (Exception ignored) {} } });
        });
    }
    private static void queueInbox() throws Exception {
        if (inboxBusy || tunnelStarting || System.currentTimeMillis() < nextInboxAttempt) return;
        JSONObject snapshot = new JSONObject();
        for (String key : new String[]{"settings", "cursors", "profile", "seed_hex", "connection"}) snapshot.put(key, data.get(key));
        final JSONObject frozen = new JSONObject(snapshot.toString()); inboxBusy = true;
        final long generation = connectionGeneration;
        inboxWorker.execute(() -> {
            JSONArray pages = new JSONArray(); boolean online = false, streaming = false;
            try {
                JSONArray relays = frozen.getJSONObject("settings").getJSONArray("relays");
                for (int j = 0; j < relays.length(); j++) {
                    String relay = relays.getString(j), contact = frozen.getJSONObject("profile").getString("id");
                    JSONObject cursors = frozen.getJSONObject("cursors");
                    String path = "/v1/sync/" + contact + "?group_after=" + cursors.optLong(relay + "|g:parano1d", 0) + "&inbox_after=" + cursors.optLong(relay + "|inbox", 0) + "&wait_ms=" + (online || !frozen.getJSONObject("connection").optBoolean("online") ? 0 : 10000);
                    try {
                        JSONObject auth = nativeResult(new JSONObject().put("op", "read_auth").put("path", path).put("seed_hex", frozen.getString("seed_hex")).put("now_ms", System.currentTimeMillis()));
                        JSONObject both = http(relay, path, null, auth);
                        pages.put(new JSONObject().put("relay", relay).put("scope", "g:parano1d").put("authenticated", false).put("page", both.getJSONObject("group")));
                        pages.put(new JSONObject().put("relay", relay).put("scope", "inbox").put("authenticated", true).put("page", both.getJSONObject("inbox")));
                        online = true; streaming = true;
                    } catch (Exception unavailable) {
                        if (!String.valueOf(unavailable.getMessage()).contains("404")) continue;
                        for (String scope : new String[]{"g:parano1d", "inbox"}) {
                            boolean authenticated = scope.equals("inbox");
                            String endpoint = authenticated ? "/v1/inbox/" + contact : "/v1/groups/parano1d/messages";
                            String legacyPath = endpoint + "?after=" + cursors.optLong(relay + "|" + scope, 0) + "&limit=30";
                            JSONObject auth = authenticated ? nativeResult(new JSONObject().put("op", "read_auth").put("path", legacyPath).put("seed_hex", frozen.getString("seed_hex")).put("now_ms", System.currentTimeMillis())) : null;
                            try { pages.put(new JSONObject().put("relay", relay).put("scope", scope).put("authenticated", authenticated).put("page", http(relay, legacyPath, null, auth))); online = true; } catch (Exception ignored) { }
                        }
                    }
                }
            } catch (Exception unavailable) { }
            final boolean connected = online, immediate = streaming;
            chatWorker.execute(() -> { inboxBusy = false;
                if (generation != connectionGeneration) { nextInboxAttempt = 0; try { queueInbox(); } catch (Exception ignored) {} return; }
                try {
                boolean reconnected = connected && (!data.has("connection") || !data.getJSONObject("connection").optBoolean("online"));
                boolean changed = !data.has("connection") || data.getJSONObject("connection").optBoolean("online") != connected;
                for (int i = 0; i < pages.length(); i++) {
                    JSONObject page = pages.getJSONObject(i); changed |= page.getJSONObject("page").getJSONArray("messages").length() > 0;
                    receivePage(page.getString("relay"), page.getString("scope"), page.getBoolean("authenticated"), page.getJSONObject("page"));
                }
                data.put("connection", new JSONObject().put("online", connected));
                if (connected) retryPendingPayments(reconnected);
                if (changed) store.save(data);
                publishView();
            } catch (Exception ignored) { } finally {
                inboxBusy = false; long delay = data.optBoolean("storage_full") ? 30000 : connected && immediate ? 100 : connected ? 2000 : 5000; nextInboxAttempt = System.currentTimeMillis() + delay;
                if (visible || DeliveryService.isRunning()) deliveryTimer.postDelayed(MainActivity::deliveryPoll, delay);
            } });
        });
    }
    private static void receivePage(String relay, String scope, boolean authenticated, JSONObject page) throws Exception {
        String cursorKey = relay + "|" + scope; JSONObject cursors = data.getJSONObject("cursors");
        long processed = cursors.optLong(cursorKey);
        if (page.getLong("cursor") < cursors.optLong(cursorKey)) throw new Exception("Relay cursor moved backwards");
        JSONArray deliveries = page.getJSONArray("messages");
        Set<String> known = new HashSet<>();
        for (String key : new String[]{"messages", "observations"}) { JSONArray list = data.getJSONArray(key); for (int i = 0; i < list.length(); i++) known.add(list.getJSONObject(i).getString("id")); }
        for (int i = 0; i < deliveries.length(); i++) {
            JSONObject envelope = deliveries.getJSONObject(i).getJSONObject("envelope");
            if (known.contains(envelope.getString("id"))) { processed = deliveries.getJSONObject(i).getLong("cursor"); continue; }
            try {
                JSONObject destination = envelope.getJSONObject("data").getJSONObject("destination");
                if (authenticated) { if (!destination.getString("type").equals("direct") || !destination.getJSONObject("contact").getString("id").equals(data.getJSONObject("profile").getString("id"))) continue; }
                else if (!destination.getString("type").equals("group") || !destination.getString("room").equals("parano1d")) continue;
                JSONObject opened = core("open", new JSONObject().put("envelope", envelope));
                JSONObject sender = opened.getJSONObject("sender"); String chat = scope;
                if (authenticated) { addContact(sender); chat = "d:" + sender.getString("id"); }
                JSONObject local = new JSONObject().put("id", opened.getString("id")).put("chat", chat).put("sender", sender).put("message", opened.getJSONObject("message")).put("created_ms", envelope.getJSONObject("data").getLong("created_ms")).put("status", "received");
                String key = local.getJSONObject("message").getString("type").equals("relay_update") ? "observations" : "messages";
                if (key.equals("observations")) { store.reserveRoom(Math.multiplyExact(4,envelope.toString().getBytes(StandardCharsets.UTF_8).length)); recordObservation(local); }
                else {
                    if (data.getJSONArray(key).length() >= 5000) throw new SecureStore.Full();
                    if (local.getJSONObject("message").optString("type").equals("transaction")) local.put("payment", core("broadcast_preview", new JSONObject().put("intent_hex", local.getJSONObject("message").getString("intent_hex"))));
                    store.reserveRoom(Math.multiplyExact(4,envelope.toString().getBytes(StandardCharsets.UTF_8).length));
                    data.getJSONArray(key).put(local);
                    notifyMessage(local);
                }
                retainEnvelope(envelope); NearbyService.offer(envelope);
                known.add(opened.getString("id"));
            } catch (SecureStore.Full full) { data.put("storage_full",true); break; }
            catch (Exception rejected) { }
            processed = deliveries.getJSONObject(i).getLong("cursor");
        }
        cursors.put(cursorKey, processed);
    }

    private void askNotificationPermission() {
        runOnUiThread(() -> {
            if (android.os.Build.VERSION.SDK_INT >= 33 && !notificationPermissionAsked && checkSelfPermission("android.permission.POST_NOTIFICATIONS") != android.content.pm.PackageManager.PERMISSION_GRANTED) {
                notificationPermissionAsked = true; requestPermissions(new String[]{"android.permission.POST_NOTIFICATIONS"}, 60);
            }
        });
    }
    private static void notifyMessage(JSONObject message) {
        try {
            String scope = message.getString("chat");
            MainActivity activity = active.get();
            boolean reading = visible && activity != null && activity.appLock != null && !activity.appLock.needsUnlock() && scope.equals(activeConversation);
            if (!scope.startsWith("d:") || reading || Math.abs(System.currentTimeMillis() - message.getLong("created_ms")) > 120000) return;
            if (message.getJSONObject("sender").getString("id").equals(data.getJSONObject("profile").getString("id"))) return;
            android.app.NotificationManager manager = application.getSystemService(android.app.NotificationManager.class);
            if (!manager.areNotificationsEnabled()) return;
            manager.createNotificationChannel(new android.app.NotificationChannel("messages", "Private messages", android.app.NotificationManager.IMPORTANCE_DEFAULT));
            int id = 1000 + Math.floorMod(scope.hashCode(),1000000);
            Intent intent = new Intent(application,MainActivity.class).addFlags(Intent.FLAG_ACTIVITY_CLEAR_TOP | Intent.FLAG_ACTIVITY_SINGLE_TOP).putExtra("open_chat",scope);
            android.app.PendingIntent open = android.app.PendingIntent.getActivity(application,id,intent,android.app.PendingIntent.FLAG_UPDATE_CURRENT | android.app.PendingIntent.FLAG_IMMUTABLE);
            boolean privatePreview = AppLock.enabled(application);
            String body = privatePreview ? "Open Paramo1d to read it." : message.getJSONObject("message").optString("text","New payment message");
            if (body.length() > 200) body = body.substring(0,200);
            manager.notify(id,new android.app.Notification.Builder(application,"messages").setSmallIcon(R.drawable.ic_message).setContentTitle(privatePreview ? "New private message" : message.getJSONObject("sender").getString("name")).setContentText(body).setVisibility(android.app.Notification.VISIBILITY_PRIVATE).setContentIntent(open).setAutoCancel(true).setGroup("paramo1d_messages").build());
        } catch (Exception ignored) { }
    }

    private static String checkEndpoint(String endpoint) throws Exception {
        URL url = new URL(endpoint); String host = url.getHost();
        boolean local = host.equals("127.0.0.1") || host.equals("localhost");
        if (!(url.getProtocol().equals("https") || url.getProtocol().equals("http") && local) || url.getUserInfo() != null || url.getRef() != null || url.getQuery() != null) throw new Exception("Use an HTTPS address or loopback HTTP");
        return endpoint.replaceAll("/+$", "");
    }
    private static JSONObject http(String base, String path, JSONObject body, JSONObject auth) throws Exception {
        if (protectedRoute) {
            JSONObject headers = new JSONObject().put("Accept", "application/json");
            if (body != null) headers.put("Content-Type", "application/json");
            if (auth != null) { headers.put("x-paramo1d-time", auth.getString("time_ms")); headers.put("x-paramo1d-signature", auth.getString("signature")); }
            return tunnelCore(new JSONObject().put("op", "request").put("url", checkEndpoint(base) + path).put("method", body == null ? "GET" : "POST").put("body", body == null ? "" : body.toString()).put("headers", headers));
        }
        return httpDirect(base, path, body, auth);
    }
    private static final okhttp3.OkHttpClient directClient = new okhttp3.OkHttpClient.Builder()
        .followRedirects(false).followSslRedirects(false)
        .connectTimeout(8, TimeUnit.SECONDS).readTimeout(12, TimeUnit.SECONDS).callTimeout(20, TimeUnit.SECONDS)
        .dns(host -> {
            java.util.ArrayList<java.net.InetAddress> addresses = new java.util.ArrayList<>();
            try { addresses.addAll(okhttp3.Dns.SYSTEM.lookup(host)); } catch (java.net.UnknownHostException unavailable) { if (!host.equals("chat.parano1d.org")) throw unavailable; }
            if (host.equals("chat.parano1d.org")) { java.net.InetAddress fallback = java.net.InetAddress.getByAddress(new byte[]{(byte)159, (byte)198, 45, 62}); if (!addresses.contains(fallback)) addresses.add(fallback); }
            return addresses;
        }).build();
    private static JSONObject httpDirect(String base, String path, JSONObject body, JSONObject auth) throws Exception {
        okhttp3.Request.Builder request = new okhttp3.Request.Builder().url(checkEndpoint(base) + path).header("Accept", "application/json");
        if (auth != null) request.header("x-paramo1d-time", auth.getString("time_ms")).header("x-paramo1d-signature", auth.getString("signature"));
        if (body != null) {
            byte[] bytes = body.toString().getBytes(StandardCharsets.UTF_8);
            if (bytes.length > 1024 * 1024) throw new Exception("Message exceeds delivery limit");
            request.post(okhttp3.RequestBody.create(bytes, okhttp3.MediaType.get("application/json")));
        }
        okhttp3.OkHttpClient routeClient = directClient;
        if (protectedRoute) {
            android.net.Network physical = physicalNetwork();
            routeClient = directClient.newBuilder().socketFactory(physical.getSocketFactory()).dns(host -> {
                java.util.ArrayList<java.net.InetAddress> addresses = new java.util.ArrayList<>();
                try { addresses.addAll(java.util.Arrays.asList(physical.getAllByName(host))); } catch (java.net.UnknownHostException unavailable) { if (!host.equals("chat.parano1d.org")) throw unavailable; }
                if (host.equals("chat.parano1d.org")) { java.net.InetAddress fallback = java.net.InetAddress.getByAddress(new byte[]{(byte)159,(byte)198,45,62}); if (!addresses.contains(fallback)) addresses.add(fallback); }
                return addresses;
            }).build();
        }
        try (okhttp3.Response response = routeClient.newCall(request.build()).execute()) {
            if (!response.isSuccessful()) throw new Exception("Relay returned " + response.code());
            if (response.body() == null) throw new Exception("Relay returned an empty reply");
            try (InputStream input = response.body().byteStream(); ByteArrayOutputStream output = new ByteArrayOutputStream()) {
                byte[] buffer = new byte[8192]; int count;
                while ((count = input.read(buffer)) >= 0) { if (output.size() + count > 4 * 1024 * 1024) throw new Exception("Delivery reply exceeds limit"); output.write(buffer, 0, count); }
                return new JSONObject(output.toString(StandardCharsets.UTF_8.name()));
            }
        }
    }

    private static android.net.Network physicalNetwork() throws Exception {
        android.net.ConnectivityManager connectivity = application.getSystemService(android.net.ConnectivityManager.class);
        android.net.Network fallback = null;
        for (android.net.Network network : connectivity.getAllNetworks()) {
            android.net.NetworkCapabilities caps = connectivity.getNetworkCapabilities(network);
            if (caps == null || !caps.hasCapability(android.net.NetworkCapabilities.NET_CAPABILITY_INTERNET) || caps.hasTransport(android.net.NetworkCapabilities.TRANSPORT_VPN)) continue;
            if (caps.hasTransport(android.net.NetworkCapabilities.TRANSPORT_WIFI) && caps.hasCapability(android.net.NetworkCapabilities.NET_CAPABILITY_VALIDATED)) return network;
            if (caps.hasCapability(android.net.NetworkCapabilities.NET_CAPABILITY_VALIDATED)) fallback = network;
        }
        if (fallback == null) throw new Exception("Connect to Wi-Fi or mobile data first");
        return fallback;
    }
    private static JSONObject tunnelCore(JSONObject request) throws Exception {
        JSONObject response = new JSONObject(NativeTunnel.call(request.toString()));
        if (!response.optBoolean("ok")) throw new Exception(response.optString("error", "Protected connection unavailable"));
        return response.getJSONObject("result");
    }
    private static void beginProtection() throws Exception {
        if (tunnelStarting) return;
        nextProtectionAttempt = System.currentTimeMillis() + 20000;
        if (data.getJSONObject("chain").optBoolean("running")) throw new Exception("Wait for the current wallet operation");
        requireIdentity();
        if (!data.has("tunnel_config")) data.put("tunnel_config", tunnelCore(new JSONObject().put("op", "keypair")));
        JSONObject config = new JSONObject(data.getJSONObject("tunnel_config").toString());
        config.put("token", randomHex(32));
        config.put("network_handle", physicalNetwork().getNetworkHandle());
        javax.net.ssl.TrustManagerFactory trust = javax.net.ssl.TrustManagerFactory.getInstance(javax.net.ssl.TrustManagerFactory.getDefaultAlgorithm());
        trust.init((java.security.KeyStore)null); JSONArray roots = new JSONArray();
        for (javax.net.ssl.TrustManager manager : trust.getTrustManagers()) if (manager instanceof javax.net.ssl.X509TrustManager) for (java.security.cert.X509Certificate certificate : ((javax.net.ssl.X509TrustManager)manager).getAcceptedIssuers()) roots.put(android.util.Base64.encodeToString(certificate.getEncoded(), android.util.Base64.NO_WRAP));
        config.put("root_certificates", roots);
        data.put("protected_route", true); connectionGeneration++; data.put("connection", new JSONObject().put("online", false)); nextInboxAttempt = 0; store.save(data); protectedRoute = true; directClient.dispatcher().cancelAll();
        core("route_set", new JSONObject().put("port", 65534).put("token", config.getString("token")));
        tunnelStarting = true; tunnelState = new JSONObject().put("enabled", true).put("checking", true);
        JSONObject auth = core("read_auth", new JSONObject().put("path", "/v1/tunnel/" + config.getString("public_key")));
        JSONObject enrollment = new JSONObject().put("id", data.getJSONObject("profile").getString("id")).put("public_key", config.getString("public_key")).put("time_ms", Long.parseLong(auth.getString("time_ms"))).put("signature", auth.getString("signature"));
        deliveryWorker.execute(() -> {
            JSONObject result = null; String problem = null;
            try {
                if (!config.has("relay_token")) { JSONObject registered = httpDirect("https://chat.parano1d.org", "/v1/tunnel/enroll", enrollment, null); for (String key : new String[]{"address", "endpoint", "server_public_key", "parameters", "relay_id", "relay_token"}) config.put(key, registered.get(key)); }
                result = tunnelCore(new JSONObject().put("op", "start").put("config", config));
                tunnelCore(new JSONObject().put("op", "request").put("url", "https://chat.parano1d.org/healthz").put("method", "GET"));
                result = tunnelCore(new JSONObject().put("op", "status"));
                if (!protectedRoute) throw new InterruptedException("Connection cancelled");
                nativeResult(new JSONObject().put("op", "route_set").put("port", result.getInt("proxy_port")).put("token", config.getString("token")));
            } catch (Exception error) { problem = error.getMessage(); if (BuildConfig.DEBUG) android.util.Log.d("Paramo1dConnection", "Protected route: " + error.getClass().getSimpleName() + ": " + problem); }
            final JSONObject checked = result; final String failure = problem;
            chatWorker.execute(() -> { try {
                tunnelStarting = false;
                if (!protectedRoute) { core("route_set", new JSONObject()); tunnelCore(new JSONObject().put("op", "stop")); tunnelState = new JSONObject().put("enabled", false); publishView(); return; }
                protectionFailures = failure == null ? 0 : protectionFailures + 1; nextProtectionAttempt = System.currentTimeMillis() + Math.min(60000, 10000L * (1 + protectionFailures)); config.remove("token"); config.remove("root_certificates"); config.remove("network_handle"); data.put("tunnel_config", config); store.save(data);
                tunnelState = new JSONObject().put("enabled", true).put("checking", false).put("connected", failure == null);
                if (failure == null && checked != null) tunnelState.put("transport", checked.optString("transport"));
                if (failure != null) tunnelState.put("problem", failure.contains("EPERM") || failure.contains("Binding socket") ? "Your other VPN blocks direct connections. Exclude Paramo1d in its per-app settings, then retry." : "Protected connection could not reach the network. Retry or connect nearby.");
                publishView(); if (failure == null) poll();
            } catch (Exception ignored) { } });
        });
    }

    private void walletScreenAwake(boolean awake) {
        runOnUiThread(() -> {
            if (isDestroyed()) return;
            if (awake) getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            else getWindow().clearFlags(android.view.WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        });
    }
    private void startChainAction(String id, JSONObject request) throws Exception {
        startChainAction(id,request,false);
    }
    private void startChainAction(String id, JSONObject request, boolean automatic) throws Exception {
        requireIdentity();
        if (data.getJSONObject("chain").optBoolean("running")) {
            if (!automatic && data.getJSONObject("chain").optBoolean("automatic") && pendingChain==null) { pendingChain=new PendingChain(this,id,new JSONObject(request.toString()));nextNodeAttempt=System.currentTimeMillis()+10000;nodeControl(false);return; }
            throw new Exception("Wait for the current wallet operation");
        }
        if (!nodeAllowed() && !request.getString("op").equals("payment_send")) throw new Exception("Open Paramo1d to update your wallet");
        if (nodeAllowed()) nodeControl(true);
        if (!automatic) nextNodeAttempt=System.currentTimeMillis()+10000;
        if (request.getString("op").equals("payment_send")) store.reserveRoom(2 * 1024 * 1024);
        if(automatic) request.put("follow",true);
        JSONObject snapshot = new JSONObject().put("seed_hex",data.getString("seed_hex")).put("settings",new JSONObject(data.getJSONObject("settings").toString()));
        snapshot.put("online",data.getJSONObject("connection").optBoolean("online"));
        if (request.getString("op").equals("payment_preview")) snapshot.put("prepared_payments",new JSONArray(data.getJSONArray("prepared_payments").toString())).put("receipts",new JSONArray(data.getJSONArray("receipts").toString()));
        if (request.getString("op").equals("payment_send")) snapshot.put("pending_review",new JSONObject(data.getJSONObject("pending_review").toString()));
        if (request.getString("op").equals("broadcast_preview") || request.getString("op").equals("broadcast_send")) {
            JSONObject found = null; JSONArray messages = data.getJSONArray("messages");
            for (int i = 0; i < messages.length(); i++) if (messages.getJSONObject(i).getString("id").equals(request.getString("message_id"))) found = messages.getJSONObject(i);
            if (found == null || !found.getJSONObject("message").getString("type").equals("transaction")) throw new Exception("Payment packet is unavailable");
            request.put("intent_hex", found.getJSONObject("message").getString("intent_hex"));
        }
        data.getJSONObject("chain").put("running", true).put("automatic",automatic);
        publishView();
        if (!automatic) walletScreenAwake(true);
        chainWorker.execute(() -> {
            final long operationStarted=android.os.SystemClock.elapsedRealtime();
            try {
                final JSONObject completed = chainAction(request, snapshot);
                postChainResult(() -> {
                    try {
                        JSONObject result = completed;
                        if(automatic && result.getJSONObject("chain").optBoolean("deferred")) {
                            data.getJSONObject("chain").put("observed_height",result.getJSONObject("chain").optLong("observed_height")).put("retrying",false).put("watched_at_ms",System.currentTimeMillis()).put("watch_ms",android.os.SystemClock.elapsedRealtime()-operationStarted);
                            nextNodeAttempt=System.currentTimeMillis()+10000;
                            return;
                        }
                        JSONObject oldChain=data.getJSONObject("chain");
                        boolean changed=!request.getString("op").equals("sync") || oldChain.optLong("height")!=result.getJSONObject("chain").optLong("height") || !oldChain.optString("block_hash").equals(result.getJSONObject("chain").optString("block_hash"));
                        data.getJSONObject("chain").put("running", false);
        if ((data.optBoolean("background_delivery") || data.optBoolean("protected_route")) && !DeliveryService.isRunning()) {
            try { application.startForegroundService(new Intent(application, DeliveryService.class)); } catch (RuntimeException requiresForeground) { }
        }
        if (data.optBoolean("protected_route") && !protectedRoute) beginProtection();
                        String op = request.getString("op");
                        if (op.equals("sync")) data.put("chain", result.getJSONObject("chain").put("running", false).put("automatic",false).put("checked_at_ms", System.currentTimeMillis()));
                        if (op.equals("payment_preview")) {
                            JSONObject wallet=result.optJSONObject("wallet"),current=data.getJSONObject("chain");
                            if(wallet!=null && wallet.optLong("balance_height")>=current.optLong("balance_height")) {
                                wallet.put("running",false).put("automatic",false).put("observed_height",current.optLong("observed_height")).put("checked_at_ms",result.optBoolean("using_saved_state")?current.optLong("checked_at_ms"):System.currentTimeMillis());
                                data.put("chain",wallet);
                            }
                            data.put("pending_review", result);
                            JSONObject publicReview = new JSONObject(result.toString()); publicReview.remove("unsigned_intent"); result = publicReview;
                        }
                        if (op.equals("payment_send")) {
                            data.remove("pending_review"); data.getJSONArray("prepared_payments").put(result);
                            store.save(data);
                            String destination = result.optString("chat");
                            if (destination.startsWith("d:")) try { sendMessage(destination, new JSONObject().put("type", "transaction").put("intent_hex", result.getString("intent_hex"))); } catch (Exception deferredChat) { result.put("chat_delivery_error", deferredChat.getMessage()); }
                            watch(result.getString("txid"), destination.startsWith("d:") ? destination : "wallet");
                            store.save(data); queueOwnBroadcast(result);
                            flushOutbox(); result = new JSONObject().put("state", view()).put("txid", result.getString("txid")).put("submitted", false).put("delivery_queued", !data.getJSONObject("settings").optString("rpc").isEmpty());
                        }
                        if (op.equals("receipt_verify")) { JSONObject receipt = result.getJSONObject("receipt"); boolean exists = false; JSONArray receipts = data.getJSONArray("receipts"); for (int i = 0; i < receipts.length(); i++) if (receipts.getJSONObject(i).getString("txid").equals(receipt.getString("txid"))) { JSONObject previous = receipts.getJSONObject(i); for (String key : new String[]{"message_id","invoice_id"}) if (receipt.optString(key).isEmpty()) receipt.put(key,previous.optString(key)); receipts.put(i,receipt); exists = true; break; } if (!exists) receipts.put(receipt); result.put("state", view()); }
                        if (op.equals("broadcast_send")) { String destination = "g:parano1d"; JSONArray messages = data.getJSONArray("messages"); for (int i = 0; i < messages.length(); i++) if (messages.getJSONObject(i).getString("id").equals(request.getString("message_id"))) destination = messages.getJSONObject(i).getString("chat"); watch(result.getString("txid"), destination); sendMessage(destination, new JSONObject().put("type", "relay_update").put("txid", result.getString("txid")).put("stage", "submitted").put("receipt_hex", JSONObject.NULL)); flushOutbox(); }
                        data.getJSONObject("chain").put("retrying",false);
                        if (!automatic || changed) store.save(data);
                        if (automatic) nextNodeAttempt=System.currentTimeMillis()+3000;
                        publishView(); reply(id, success(op.equals("sync") ? view() : result));
                    } catch (Exception error) { if(automatic)nextNodeAttempt=System.currentTimeMillis()+15000;reply(id, failure(error)); }
                    finally { finishChainAction(); }
                });
            } catch (Exception error) { postChainResult(() -> { try { if(automatic){nextNodeAttempt=System.currentTimeMillis()+15000;data.getJSONObject("chain").put("retrying",nodeAllowed());} reply(id, failure(error)); } catch(Exception ignored){} finally {finishChainAction();} }); }
            finally { walletScreenAwake(false); }
        });
    }
    private static void postChainResult(Runnable result) {
        // A completed wallet operation must reach the state worker even when
        // the bounded queue is temporarily full. Only the wallet worker waits.
        try { chatWorker.execute(result); }
        catch (java.util.concurrent.RejectedExecutionException full) {
            try { ((ThreadPoolExecutor)chatWorker).getQueue().put(result); }
            catch (InterruptedException interrupted) { Thread.currentThread().interrupt(); }
        }
    }
    private void finishChainAction() {
        try {
            data.getJSONObject("chain").put("running",false).put("automatic",false); publishView();
            PendingChain pending=pendingChain; pendingChain=null;
            if(pending!=null) {try{pending.owner.startChainAction(pending.id,pending.request,false);}catch(Exception error){pending.owner.reply(pending.id,failure(error));}}
        } catch(Exception ignored){}
    }
    private JSONObject chainAction(JSONObject request, JSONObject snapshot) throws Exception {
        String op = request.getString("op");
        String rpc = snapshot.getJSONObject("settings").optString("rpc");
        File artifacts = new File(getFilesDir(), "artifacts"); File chain = new File(getFilesDir(), "chain");
        if (op.equals("broadcast_send") && rpc.isEmpty()) throw new Exception("Add a chain data endpoint in Settings");
        if (op.equals("sync") || op.equals("payment_preview")) {
            installParameters(artifacts);
            if (!new File(artifacts, "legacy").isFile()) throw new Exception("Install the released verification parameters to synchronize");
            if (op.equals("payment_preview") && rpc.isEmpty() && !request.optBoolean("use_cached")) throw new Exception("Add a chain data endpoint in Settings");
            JSONObject args = new JSONObject(request.toString()).put("artifacts", artifacts.getAbsolutePath()).put("data_dir", chain.getAbsolutePath()).put("rpc", rpc).put("seed_hex", snapshot.getString("seed_hex"));
            if (op.equals("payment_preview")) {
                args.put("online",snapshot.optBoolean("online"));
                JSONArray reservations = new JSONArray(), prepared = snapshot.getJSONArray("prepared_payments"), receipts = snapshot.getJSONArray("receipts");
                for (int i = 0; i < prepared.length(); i++) {
                    JSONObject packet = prepared.getJSONObject(i);
                    if (!packet.has("reservation")) continue;
                    JSONObject reservation = new JSONObject(packet.getJSONObject("reservation").toString());
                    for (int j = 0; j < receipts.length(); j++) { JSONObject receipt = receipts.getJSONObject(j); if (receipt.optBoolean("verified") && receipt.optString("txid").equals(packet.getString("txid"))) reservation.put("included_height", receipt.getLong("height")); }
                    reservations.put(reservation);
                }
                return nativeResult(args.put("reservations", reservations)).put("chat", request.optString("chat")).put("invoice_id", request.optString("invoice_id"));
            }
            if (!rpc.isEmpty()) return new JSONObject().put("chain", nativeResult(args.put("op", "wallet_sync")));
            JSONObject synced = nativeResult(args.put("op", "sync_once")); return new JSONObject().put("chain", synced.getJSONObject("verified"));
        }
        if (op.equals("payment_send")) {
            JSONObject review = snapshot.getJSONObject("pending_review");
            if (!review.getString("review_id").equals(request.getString("review_id"))) throw new Exception("Payment review has changed");
            JSONObject authorized = nativeResult(new JSONObject().put("op", "payment_authorize").put("seed_hex", snapshot.getString("seed_hex")).put("review_id", review.getString("review_id")).put("unsigned_intent", review.getString("unsigned_intent")));
            authorized.put("chat", review.optString("chat")).put("invoice_id", review.optString("invoice_id"));
            for (String key : new String[]{"to", "amount", "fee"}) authorized.put(key, review.get(key));
            authorized.put("submitted", false).put("created_ms", System.currentTimeMillis());
            return authorized;
        }
        if (op.equals("receipt_verify")) {
            installParameters(artifacts);
            JSONObject args = new JSONObject(request.toString()).put("op", "receipt_check").put("artifacts", artifacts.getAbsolutePath()).put("data_dir", chain.getAbsolutePath());
            JSONObject accepted = new JSONObject(new String(java.nio.file.Files.readAllBytes(new File(chain, "accepted.json").toPath()), StandardCharsets.UTF_8));
            args.put("bundle", new File(chain, accepted.getString("bundle")).getAbsolutePath());
            JSONObject receipt = nativeResult(args).put("message_id", request.optString("message_id")).put("invoice_id", request.optString("invoice_id")).put("receipt_hex", request.getString("receipt_hex"));
            return new JSONObject().put("receipt", receipt);
        }
        JSONObject args = new JSONObject(request.toString()).put("rpc", rpc).put("seed_hex", snapshot.getString("seed_hex"));
        return nativeResult(args);
    }

    private void installParameters(File directory) throws Exception {
        if (!directory.isDirectory() && !directory.mkdirs()) throw new Exception("Cannot prepare verification storage");
        String[] files = getAssets().list("parameters");
        if (files == null || files.length == 0) throw new Exception("Build the APK with the released verification parameters");
        String release;
        try (java.io.BufferedReader input = new java.io.BufferedReader(new java.io.InputStreamReader(getAssets().open("parameters/release.id"), StandardCharsets.UTF_8))) { release = input.readLine(); }
        if (release == null || !release.matches("[0-9a-f]{64}")) throw new Exception("Invalid verification release identity");
        File marker = new File(directory, ".release"); boolean complete = marker.isFile() && release.equals(new String(java.nio.file.Files.readAllBytes(marker.toPath()), StandardCharsets.UTF_8));
        for (String name : files) complete &= new File(directory, name).isFile();
        if (complete) return;
        for (String name : files) {
            if (!name.matches("[a-z0-9.-]{1,64}")) throw new Exception("Invalid verification parameter name");
            File target = new File(directory, name);
            android.util.AtomicFile file = new android.util.AtomicFile(target); java.io.FileOutputStream output = null;
            try (InputStream input = getAssets().open("parameters/" + name)) {
                output = file.startWrite(); byte[] buffer = new byte[65536]; int count;
                while ((count = input.read(buffer)) != -1) output.write(buffer, 0, count);
                file.finishWrite(output);
            } catch (Exception error) { if (output != null) file.failWrite(output); throw error; }
        }
        android.util.AtomicFile record = new android.util.AtomicFile(marker); java.io.FileOutputStream output = record.startWrite();
        try { output.write(release.getBytes(StandardCharsets.UTF_8)); record.finishWrite(output); } catch (Exception error) { record.failWrite(output); throw error; }
    }

    @Override protected void onActivityResult(int request, int result, Intent intent) {
        super.onActivityResult(request, result, intent);
        if (appLock.activityResult(request, result)) return;
        if (unlockedSystemFlows.remove(request)) appLock.opened();
        if ((request == 40 || request == 41) && backupPickerActive) { backupPickerActive = false; appLock.opened(); }
        if (request == 40 && result == RESULT_OK && intent != null && pendingBackup != null) {
            String backup = pendingBackup; pendingBackup = null;
            chatWorker.execute(() -> { try {
                try (OutputStream output = getContentResolver().openOutputStream(intent.getData())) { if (output == null) throw new Exception("Cannot write backup"); output.write(backup.getBytes(StandardCharsets.UTF_8)); }
                data.put("backup_saved_ms", System.currentTimeMillis()); store.save(data); publishView();
                runOnUiThread(() -> android.widget.Toast.makeText(this, "Backup saved. Keep its password separately.", android.widget.Toast.LENGTH_LONG).show());
            } catch (Exception ignored) { runOnUiThread(() -> android.widget.Toast.makeText(this, "Backup could not be saved. Please try again.", android.widget.Toast.LENGTH_LONG).show()); } });
        } else if (request == 40) pendingBackup = null;
        if (request == 41 && result == RESULT_OK && intent != null && pendingRestorePassword != null) {
            String password = pendingRestorePassword; pendingRestorePassword = null;
            chatWorker.execute(() -> { try (InputStream input = getContentResolver().openInputStream(intent.getData()); ByteArrayOutputStream output = new ByteArrayOutputStream()) {
                if (input == null) throw new Exception("Cannot read backup"); byte[] buffer = new byte[8192]; int count;
                while ((count = input.read(buffer)) != -1) { if (output.size() + count > 65 * 1024 * 1024) throw new Exception("Backup exceeds size limit"); output.write(buffer, 0, count); }
                handle(new JSONObject().put("op", "backup_restore").put("password", password).put("backup", output.toString(StandardCharsets.UTF_8.name())));
                runOnUiThread(() -> { if (!isDestroyed()) web.reload(); });
            } catch (Exception error) { runOnUiThread(() -> android.widget.Toast.makeText(this, error.getMessage(), android.widget.Toast.LENGTH_LONG).show()); } });
        } else if (request == 41) pendingRestorePassword = null;
        if (request == 62 && result == RESULT_OK) startNearby();
        if (request == 63) NearbyService.scan();
    }
    private void startNearby() {
        try {
            String[] required = android.os.Build.VERSION.SDK_INT >= 31 ? new String[]{"android.permission.BLUETOOTH_SCAN", "android.permission.BLUETOOTH_CONNECT", "android.permission.BLUETOOTH_ADVERTISE"} : new String[]{"android.permission.ACCESS_FINE_LOCATION"};
            java.util.ArrayList<String> missing = new java.util.ArrayList<>(); for (String permission : required) if (checkSelfPermission(permission) != android.content.pm.PackageManager.PERMISSION_GRANTED) missing.add(permission);
            if (android.os.Build.VERSION.SDK_INT >= 33 && !notificationPermissionAsked && checkSelfPermission("android.permission.POST_NOTIFICATIONS") != android.content.pm.PackageManager.PERMISSION_GRANTED) { notificationPermissionAsked = true; missing.add("android.permission.POST_NOTIFICATIONS"); }
            if (!missing.isEmpty()) { requestPermissions(missing.toArray(new String[0]), 61); return; }
            android.bluetooth.BluetoothAdapter adapter = getSystemService(android.bluetooth.BluetoothManager.class).getAdapter();
            if (adapter == null) throw new Exception("Bluetooth is unavailable on this device");
            if (!adapter.isEnabled()) { startActivityForResult(new Intent(android.bluetooth.BluetoothAdapter.ACTION_REQUEST_ENABLE), 62); return; }
            startForegroundService(new Intent(this, NearbyService.class));
            startActivityForResult(new Intent(android.bluetooth.BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE).putExtra(android.bluetooth.BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, 120), 63);
        } catch (Exception error) { android.widget.Toast.makeText(this, error.getMessage(), android.widget.Toast.LENGTH_LONG).show(); }
    }
    @Override public void onRequestPermissionsResult(int request, String[] permissions, int[] grants) {
        super.onRequestPermissionsResult(request, permissions, grants);
        if (request == 60 || request == 61) appLock.opened();
        if (request == 60) { chatWorker.execute(() -> { try { if (data != null) publishView(); } catch (Exception ignored) {} }); return; }
        if (request != 61) return;
        boolean allowed = true;
        for (int i = 0; i < permissions.length; i++) if (!permissions[i].equals("android.permission.POST_NOTIFICATIONS") && grants[i] != android.content.pm.PackageManager.PERMISSION_GRANTED) allowed = false;
        if (allowed) {
            try { android.bluetooth.BluetoothAdapter adapter = getSystemService(android.bluetooth.BluetoothManager.class).getAdapter(); if (adapter == null) throw new Exception("Bluetooth unavailable"); if (!adapter.isEnabled()) startActivityForResult(new Intent(android.bluetooth.BluetoothAdapter.ACTION_REQUEST_ENABLE), 62); else { startForegroundService(new Intent(this, NearbyService.class)); startActivityForResult(new Intent(android.bluetooth.BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE).putExtra(android.bluetooth.BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, 120), 63); } }
            catch (Exception error) { android.widget.Toast.makeText(this, error.getMessage(), android.widget.Toast.LENGTH_LONG).show(); }
        } else android.widget.Toast.makeText(this, "Nearby needs permission to connect to nearby devices. Internet chat remains available.", android.widget.Toast.LENGTH_LONG).show();
    }
    private static void watch(String txid, String chat) throws Exception {
        JSONArray old = data.getJSONArray("watches"), watches = new JSONArray(); long now = System.currentTimeMillis();
        for (int i = 0; i < old.length(); i++) { JSONObject item = old.getJSONObject(i); if (now - item.optLong("created_ms", now) < 3600000 && !item.optString("stage").equals("included")) watches.put(item); }
        data.put("watches", watches);
        for (int i = 0; i < watches.length(); i++) if (watches.getJSONObject(i).getString("txid").equals(txid) && watches.getJSONObject(i).getString("chat").equals(chat)) return;
        if (watches.length() < 20) watches.put(new JSONObject().put("txid", txid).put("chat", chat).put("created_ms", now).put("last_ms", 0).put("stage", "submitted"));
    }
    private static void queueOwnBroadcast(JSONObject packet) throws Exception {
        String rpc = data.getJSONObject("settings").optString("rpc"); if (rpc.isEmpty()) return;
        String txid = packet.getString("txid"); if (!sendingPayments.add(txid)) return;
        packet.put("last_delivery_ms", System.currentTimeMillis());
        final JSONObject frozen = new JSONObject(packet.toString());
        try { paymentDeliveryWorker.execute(() -> {
            String failure = null;
            try { nativeResult(new JSONObject(frozen.toString()).put("op", "broadcast_send").put("rpc", rpc)); }
            catch (Exception error) { failure = error.getMessage(); }
            final String error = failure;
            chatWorker.execute(() -> { try {
                JSONArray packets = data.getJSONArray("prepared_payments");
                for (int i = 0; i < packets.length(); i++) if (packets.getJSONObject(i).getString("txid").equals(frozen.getString("txid"))) { packets.getJSONObject(i).put("submitted", error == null); if (error != null) packets.getJSONObject(i).put("delivery_error", error.substring(0, Math.min(300, error.length()))); else packets.getJSONObject(i).remove("delivery_error"); }
                if (error == null) { JSONObject message = new JSONObject().put("type", "relay_update").put("txid", frozen.getString("txid")).put("stage", "submitted").put("receipt_hex", JSONObject.NULL); if (frozen.optString("chat").startsWith("d:")) sendMessage(frozen.getString("chat"), message); else recordObservation(new JSONObject().put("id", randomHex(32)).put("sender", data.getJSONObject("profile")).put("chat", "wallet").put("created_ms", System.currentTimeMillis()).put("message", message)); }
                store.save(data); flushOutbox(); publishView();
            } catch (Exception ignored) { } finally { sendingPayments.remove(txid); } });
        }); } catch (java.util.concurrent.RejectedExecutionException busy) { sendingPayments.remove(txid); }
    }
    private static void retryPendingPayments(boolean reconnected) throws Exception {
        if (!data.getJSONObject("connection").optBoolean("online") || tunnelStarting) return;
        long now = System.currentTimeMillis(); JSONArray packets = data.getJSONArray("prepared_payments"), receipts = data.getJSONArray("receipts");
        for (int i = 0; i < packets.length(); i++) { JSONObject packet = packets.getJSONObject(i);
            if (packet.optBoolean("submitted") || sendingPayments.contains(packet.getString("txid")) || now - packet.optLong("created_ms",now) >= 3600000 || !reconnected && now - packet.optLong("last_delivery_ms") < 30000) continue;
            boolean checked = false; for (int j = 0; j < receipts.length(); j++) if (receipts.getJSONObject(j).optBoolean("verified") && receipts.getJSONObject(j).optString("txid").equals(packet.getString("txid"))) { checked = true; break; }
            if (!checked) { queueOwnBroadcast(packet); break; }
        }
    }
    private static void recordObservation(JSONObject observation) throws Exception {
        JSONArray old = data.getJSONArray("observations"), next = new JSONArray();
        String sender = observation.getJSONObject("sender").getString("id"); String txid = observation.getJSONObject("message").getString("txid");
        for (int i = 0; i < old.length(); i++) { JSONObject previous = old.getJSONObject(i); boolean same = previous.getJSONObject("sender").getString("id").equals(sender) && previous.getJSONObject("message").getString("txid").equals(txid);
            if (same && previous.getLong("created_ms") > observation.getLong("created_ms")) return;
            if (!same) next.put(previous);
        }
        if (next.length() < 2000) next.put(observation); data.put("observations", next);
    }
    private static void scheduleObservations() throws Exception {
        String rpc = data.getJSONObject("settings").optString("rpc"); if (rpc.isEmpty()) return;
        JSONArray watches = data.getJSONArray("watches"); long now = System.currentTimeMillis();
        for (int i = 0; i < watches.length(); i++) {
            JSONObject watched = watches.getJSONObject(i);
            if (now - watched.optLong("last_ms") < 30000 || watched.optString("stage").equals("included") || now - watched.optLong("created_ms", now) >= 3600000) continue;
            watched.put("last_ms", now); String txid = watched.getString("txid"); String destination = watched.getString("chat");
            chainWorker.execute(() -> {
                try { JSONObject status = nativeResult(new JSONObject().put("op", "transaction_status").put("rpc", rpc).put("txid", txid));
                    chatWorker.execute(() -> { try {
                        String stage = status.getString("stage"); if (!(stage.equals("included") || stage.equals("in_mempool"))) return;
                        boolean changed = !watched.getString("stage").equals(stage); if (!changed && System.currentTimeMillis() - watched.optLong("published_ms") < 120000) return;
                        watched.put("stage", stage).put("published_ms", System.currentTimeMillis());
                        JSONObject message = new JSONObject().put("type", "relay_update").put("txid", txid).put("stage", stage).put("receipt_hex", status.opt("receipt_hex"));
                        if (destination.equals("wallet")) recordObservation(new JSONObject().put("id", randomHex(32)).put("sender", data.getJSONObject("profile")).put("chat", "wallet").put("created_ms", System.currentTimeMillis()).put("message", message)); else sendMessage(destination, message);
                        flushOutbox(); store.save(data);
                    } catch (Exception ignored) {} });
                } catch (Exception ignored) {}
            });
            break;
        }
    }
    static void initializeDelivery(android.content.Context context) {
        application = context.getApplicationContext();
        chatWorker.execute(() -> { try {
            if (store == null) store = new SecureStore(application);
            if (data == null) { data = store.read(); initializeFields(); }
            if (!data.has("seed_hex") || !(data.optBoolean("background_delivery",true) || data.optBoolean("protected_route"))) application.stopService(new Intent(application,DeliveryService.class));
        } catch (Exception ignored) { } });
    }
    static void deliveryPoll() {
        chatWorker.execute(() -> { try { if (data != null && data.has("seed_hex")) { poll(); publishView(); } } catch (Exception ignored) { } });
    }
    static void stopDelivery() {
        chatWorker.execute(() -> { try {
            if (data == null) return;
            data.put("background_delivery", false).put("protected_route", false); store.save(data);
            if (protectedRoute) { connectionGeneration++; data.put("connection", new JSONObject().put("online", false)); nextInboxAttempt = 0; }
            protectedRoute = false; core("route_set", new JSONObject()); tunnelCore(new JSONObject().put("op", "stop"));
            tunnelState = new JSONObject().put("enabled", false); publishView();
        } catch (Exception ignored) { } });
    }
    private static void publishView() throws Exception {
        final JSONObject updated = view(); MainActivity activity = active.get();
        if (activity != null && activity.appLock != null && activity.appLock.needsUnlock()) return;
        final boolean checking = updated.optJSONObject("chain").optBoolean("running") && !updated.optJSONObject("chain").optBoolean("automatic");
        final String script = "window.paramo1dUpdate(" + updated.toString() + ")";
        if (activity != null) activity.runOnUiThread(() -> { if (!activity.isDestroyed()) {
            if (checking) activity.getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            else activity.getWindow().clearFlags(android.view.WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            activity.web.evaluateJavascript(script, null);
        } });
    }
    private static void retainEnvelope(JSONObject envelope) throws Exception {
        JSONArray history = data.getJSONArray("envelopes"), next = new JSONArray(); long now = System.currentTimeMillis();
        next.put(envelope); int bytes = envelope.toString().length();
        for (int i = history.length() - 1; i >= 0 && next.length() < 128; i--) { JSONObject item = history.getJSONObject(i); int size = item.toString().length();
            if (!item.getString("id").equals(envelope.getString("id")) && item.getJSONObject("data").getLong("expires_ms") > now && bytes + size <= 4 * 1024 * 1024) { next.put(item); bytes += size; }
        }
        data.put("envelopes", next);
    }
    static java.util.concurrent.CompletableFuture<JSONObject> nearbyCall(String action, JSONObject args) {
        java.util.concurrent.CompletableFuture<JSONObject> future = new java.util.concurrent.CompletableFuture<>();
        try { chatWorker.execute(() -> { try {
            requireIdentity(); JSONObject result = new JSONObject();
            if (action.equals("hello")) result.put("invite", data.getString("invite")).put("contact", data.getJSONObject("profile"));
            else if (action.equals("sign")) result = core("read_auth", args);
            else if (action.equals("verify")) result = core("verify_link", args);
            else if (action.equals("encrypt")) result = core("link_encrypt", args);
            else if (action.equals("decrypt")) result = core("link_decrypt", args);
            else if (action.equals("contact")) result = core("contact_import", args);
            else if (action.equals("connected")) { addContact(args.getJSONObject("contact")); publishView(); }
            else if (action.equals("inventory")) {
                JSONArray ids = new JSONArray(); Set<String> known = new HashSet<>(); long now = System.currentTimeMillis();
                for (String key : new String[]{"outbox", "envelopes"}) { JSONArray list = data.getJSONArray(key); for (int i = 0; i < list.length() && ids.length() < 128; i++) { JSONObject envelope = list.getJSONObject(i); String id = envelope.getString("id"); if (envelope.getJSONObject("data").getLong("expires_ms") > now && known.add(id)) ids.put(id); } }
                result.put("ids", ids);
            } else if (action.equals("missing")) {
                JSONArray wanted = new JSONArray(), requested = args.getJSONArray("ids"); if (requested.length() > 128) throw new Exception("Nearby inventory exceeds limit"); Set<String> known = new HashSet<>();
                for (String key : new String[]{"envelopes", "messages", "observations"}) { JSONArray list = data.getJSONArray(key); for (int i = 0; i < list.length(); i++) known.add(list.getJSONObject(i).getString("id")); }
                for (int i = 0; i < requested.length() && wanted.length() < 8; i++) { String id = requested.getString(i); if (id.matches("[0-9a-f]{64}") && !known.contains(id)) wanted.put(id); }
                result.put("ids", wanted);
            } else if (action.equals("packets")) {
                JSONArray requested = args.getJSONArray("ids"); if (requested.length() > 8) throw new Exception("Nearby request exceeds limit"); Set<String> wanted = new HashSet<>(); for (int i = 0; i < requested.length(); i++) wanted.add(requested.getString(i));
                JSONArray packets = new JSONArray(); for (String key : new String[]{"outbox", "envelopes"}) { JSONArray list = data.getJSONArray(key); for (int i = 0; i < list.length(); i++) { JSONObject item = list.getJSONObject(i); if (wanted.remove(item.getString("id"))) packets.put(item); } } result.put("envelopes", packets);
            } else if (action.equals("accept")) result = acceptNearby(args.getJSONObject("envelope"));
            else if (action.equals("ack")) { JSONArray messages = data.getJSONArray("messages"); for (int i = 0; i < messages.length(); i++) if (messages.getJSONObject(i).getString("id").equals(args.getString("id"))) messages.getJSONObject(i).put("nearby_delivered", true); store.save(data); publishView(); }
            else if (action.equals("poll")) poll();
            else if (action.equals("updated")) publishView();
            else throw new Exception("Unknown nearby action");
            future.complete(new JSONObject(result.toString()));
        } catch (Exception error) { future.completeExceptionally(error); } }); } catch (Exception error) { future.completeExceptionally(error); }
        return future;
    }
    private static JSONObject acceptNearby(JSONObject envelope) throws Exception {
        String id = envelope.getString("id");
        for (String key : new String[]{"envelopes", "messages", "observations"}) { JSONArray list = data.getJSONArray(key); for (int i = 0; i < list.length(); i++) if (list.getJSONObject(i).getString("id").equals(id)) return new JSONObject().put("id", id).put("new", false); }
        JSONObject destination = envelope.getJSONObject("data").getJSONObject("destination"); boolean direct = destination.getString("type").equals("direct");
        if (!direct && (!destination.getString("type").equals("group") || !destination.getString("room").equals("parano1d"))) throw new Exception("Unknown nearby channel");
        boolean own = direct && destination.getJSONObject("contact").getString("id").equals(data.getJSONObject("profile").getString("id"));
        JSONObject opened = core(own || !direct ? "open" : "verify_envelope", new JSONObject().put("envelope", envelope));
        int queued = data.getJSONArray("outbox").toString().length(); if (queued + envelope.toString().length() > 4 * 1024 * 1024) throw new Exception("Delivery queue is full");
        if (own || !direct) {
            JSONObject sender = opened.getJSONObject("sender"); if (own) addContact(sender);
            JSONObject message = opened.getJSONObject("message");
            JSONObject local = new JSONObject().put("id", id).put("chat", own ? "d:" + sender.getString("id") : "g:parano1d").put("sender", sender).put("message", message).put("created_ms", envelope.getJSONObject("data").getLong("created_ms")).put("status", "received").put("via_nearby", true);
            if (message.getString("type").equals("relay_update")) { store.reserveRoom(Math.multiplyExact(4,envelope.toString().getBytes(StandardCharsets.UTF_8).length)); recordObservation(local); }
            else { if (data.getJSONArray("messages").length() >= 5000) throw new SecureStore.Full(); if (message.getString("type").equals("transaction")) local.put("payment", core("broadcast_preview", new JSONObject().put("intent_hex", message.getString("intent_hex")))); store.reserveRoom(Math.multiplyExact(4,envelope.toString().getBytes(StandardCharsets.UTF_8).length)); data.getJSONArray("messages").put(local); notifyMessage(local); }
        } else store.reserveRoom(Math.multiplyExact(4,envelope.toString().getBytes(StandardCharsets.UTF_8).length));
        retainEnvelope(envelope); data.getJSONArray("outbox").put(envelope); store.save(data); queueDelivery(); publishView();
        return new JSONObject().put("id", id).put("new", true);
    }
    @Override protected void onDestroy() { nodeTimer.removeCallbacks(nodeTick);try{unregisterReceiver(screenOff);}catch(Exception ignored){}if (appLock != null) appLock.destroy(); if (active.get() == this) {pauseNode();active.clear();} web.removeJavascriptInterface("Paramo1d"); web.destroy(); super.onDestroy(); }
    private void applySystemTheme(String selected) {
        boolean dark = selected.equals("dark") || selected.equals("system") && (getResources().getConfiguration().uiMode & android.content.res.Configuration.UI_MODE_NIGHT_MASK) == android.content.res.Configuration.UI_MODE_NIGHT_YES;
        int paper=dark?Color.rgb(16,20,19):Color.rgb(246,246,238);
        getWindow().setBackgroundDrawable(new android.graphics.drawable.ColorDrawable(paper));
        getWindow().getDecorView().setBackgroundColor(paper);
        if(root!=null) root.setBackgroundColor(paper);
        if(web!=null) web.setBackgroundColor(paper);
        getWindow().setStatusBarColor(paper);
        getWindow().setNavigationBarColor(paper);
        if(android.os.Build.VERSION.SDK_INT>=29) {
            getWindow().setStatusBarContrastEnforced(false);
            getWindow().setNavigationBarContrastEnforced(false);
        }
        if(android.os.Build.VERSION.SDK_INT>=30) {
            android.view.WindowInsetsController controller=getWindow().getInsetsController();
            if(controller!=null) {
                int appearance=android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS | android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS;
                controller.setSystemBarsAppearance(dark?0:appearance,appearance);
            }
        } else {
            int mask=android.view.View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | android.view.View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
            int flags=getWindow().getDecorView().getSystemUiVisibility();
            getWindow().getDecorView().setSystemUiVisibility((flags & ~mask) | (dark?0:mask));
        }
    }
    @Override public void onConfigurationChanged(android.content.res.Configuration configuration) {
        super.onConfigurationChanged(configuration);
        applySystemTheme(getSharedPreferences("interface",MODE_PRIVATE).getString("theme","system"));
        if(root!=null) root.requestApplyInsets();
    }
    @Override public void onTrimMemory(int level) {
        super.onTrimMemory(level);
        if(level>=android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_LOW && level!=android.content.ComponentCallbacks2.TRIM_MEMORY_UI_HIDDEN) {
            try { NativeCore.call(new JSONObject().put("op","node_trim_memory").toString()); } catch(Throwable ignored) {}
        }
    }
    @Override public void onBackPressed() {
        if (appLock.needsUnlock()) { moveTaskToBack(true); return; }
        web.evaluateJavascript("window.paramo1dBack ? window.paramo1dBack() : false", handled -> {
            if (!"true".equals(handled)) moveTaskToBack(true);
        });
    }
}
