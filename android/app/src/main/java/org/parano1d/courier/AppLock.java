package org.parano1d.courier;

import android.app.Activity;
import android.app.KeyguardManager;
import android.content.Context;
import android.content.Intent;
import android.hardware.biometrics.BiometricManager;
import android.hardware.biometrics.BiometricPrompt;
import android.os.Build;
import android.os.CancellationSignal;
import android.os.SystemClock;
import org.json.JSONObject;
import java.io.File;

/** Phone authentication protects entry to the UI. Background delivery stays independent. */
final class AppLock {
    private static final int CREDENTIAL_REQUEST = 81;
    private static final long AWAY_MS = 30_000;
    private static volatile boolean open;
    private static volatile long awayAt;
    private final Activity activity;
    private Runnable approved, cancelled;
    private CancellationSignal signal;
    private BiometricPrompt prompt;
    private boolean authenticating;
    private long attempt, startedAt;

    AppLock(Activity activity) { this.activity = activity; }
    static boolean available(Context context) { return context.getSystemService(KeyguardManager.class).isDeviceSecure(); }
    static boolean enabled(Context context) {
        android.content.SharedPreferences preferences = context.getSharedPreferences("app-lock", Context.MODE_PRIVATE);
        if (preferences.contains("enabled")) return preferences.getBoolean("enabled", false);
        boolean protect = available(context) && new File(context.getFilesDir(), "identity.pmc").isFile();
        if (protect) preferences.edit().putBoolean("enabled", true).apply();
        return protect;
    }
    static void setEnabled(Context context, boolean enabled) {
        if (enabled && !available(context)) throw new IllegalStateException("Set a phone PIN or fingerprint first.");
        context.getSharedPreferences("app-lock", Context.MODE_PRIVATE).edit().putBoolean("enabled", enabled).apply();
    }
    static JSONObject state(Context context) throws Exception {
        return new JSONObject().put("available", available(context)).put("enabled", enabled(context)).put("away_seconds", AWAY_MS / 1000);
    }
    boolean needsUnlock() {
        boolean wallet = new File(activity.getFilesDir(), "identity.pmc").isFile();
        return wallet && enabled(activity) && (!open || awayAt != 0 && SystemClock.elapsedRealtime() - awayAt >= AWAY_MS);
    }
    void opened() { open = true; awayAt = 0; }
    void backgrounded() { awayAt = SystemClock.elapsedRealtime(); }
    void lock() { open = false; }
    boolean authenticating() { return authenticating; }
    void authenticate(Runnable success, Runnable cancel) {
        if (authenticating) {
            if (!activity.hasWindowFocus() || SystemClock.elapsedRealtime() - startedAt < 1000) return;
            cancelAuthentication();
        }
        if (!available(activity)) { cancel.run(); return; }
        approved = success; cancelled = cancel; authenticating = true; startedAt = SystemClock.elapsedRealtime();
        final long current = ++attempt;
        android.util.Log.i("Paramo1dUnlock", "Authentication requested with focused window=" + activity.hasWindowFocus());
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                BiometricPrompt.Builder builder = new BiometricPrompt.Builder(activity)
                    .setTitle("Unlock Paramo1d")
                    .setSubtitle("Use your fingerprint or phone PIN");
                if (Build.VERSION.SDK_INT >= 30) builder.setAllowedAuthenticators(BiometricManager.Authenticators.BIOMETRIC_STRONG | BiometricManager.Authenticators.DEVICE_CREDENTIAL);
                else builder.setDeviceCredentialAllowed(true);
                signal = new CancellationSignal();
                prompt = builder.build();
                prompt.authenticate(signal, activity.getMainExecutor(), new BiometricPrompt.AuthenticationCallback() {
                    @Override public void onAuthenticationSucceeded(BiometricPrompt.AuthenticationResult result) { complete(current, true); }
                    @Override public void onAuthenticationError(int code, CharSequence text) {
                        android.util.Log.i("Paramo1dUnlock", "Authentication ended with code=" + code);
                        complete(current, false);
                    }
                });
            } else {
                Intent intent = activity.getSystemService(KeyguardManager.class).createConfirmDeviceCredentialIntent("Unlock Paramo1d", "Use your phone screen lock");
                if (intent == null) complete(current, false); else activity.startActivityForResult(intent, CREDENTIAL_REQUEST);
            }
        } catch (RuntimeException unavailable) {
            android.util.Log.w("Paramo1dUnlock", "Authentication could not start");
            complete(current, false);
        }
    }
    boolean activityResult(int request, int result) {
        if (request != CREDENTIAL_REQUEST) return false;
        if (authenticating && signal == null) complete(attempt, result == Activity.RESULT_OK);
        return true;
    }
    private void complete(long current, boolean success) {
        if (current != attempt || !authenticating) return;
        Runnable callback = success ? approved : cancelled;
        authenticating = false; approved = null; cancelled = null; signal = null; prompt = null;
        android.util.Log.i("Paramo1dUnlock", success ? "Authentication accepted" : "Authentication cancelled");
        if (success) opened();
        if (callback != null && !activity.isDestroyed()) callback.run();
    }
    private void cancelAuthentication() {
        CancellationSignal pending = signal;
        ++attempt; authenticating = false; approved = null; cancelled = null; signal = null; prompt = null;
        if (pending != null) { android.util.Log.i("Paramo1dUnlock", "Cancelling pending authentication"); pending.cancel(); }
    }
    void destroy() { cancelAuthentication(); }
}
