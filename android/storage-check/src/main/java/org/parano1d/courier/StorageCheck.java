package org.parano1d.courier;

import android.app.Activity;
import android.app.Instrumentation;
import android.content.Context;
import android.os.Bundle;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import org.json.JSONArray;
import org.json.JSONObject;

/** Runs the production storage and backup code under a separate Android UID. */
public final class StorageCheck extends Instrumentation {
    private static final String PACKAGE = "org.parano1d.courier.storagecheck";
    private static final String SEED = "5555555555555555555555555555555555555555555555555555555555555555";
    private static final String PASSWORD = "unfunded device backup fixture";
    private Bundle arguments;
    private int checks;

    @Override public void onCreate(Bundle arguments) {
        super.onCreate(arguments);
        this.arguments = arguments == null ? new Bundle() : arguments;
        start();
    }

    private void require(boolean condition, String label) {
        if (!condition) throw new AssertionError(label);
        checks++;
    }

    private JSONObject call(JSONObject request) throws Exception {
        return new JSONObject(NativeCore.call(request.toString()));
    }

    private JSONObject result(JSONObject request) throws Exception {
        JSONObject response = call(request);
        require(response.getBoolean("ok"), "Native fixture operation");
        return response.getJSONObject("result");
    }

    private JSONObject fixture() throws Exception {
        JSONObject profile = result(new JSONObject().put("op", "profile").put("seed_hex", SEED).put("name", "Unfunded storage fixture"));
        return new JSONObject().put("seed_hex", SEED).put("profile", profile.getJSONObject("contact"))
            .put("messages", new JSONArray().put(new JSONObject().put("text", "Hello 🌍 Welcome")))
            .put("receipts", new JSONArray()).put("prepared_payments", new JSONArray());
    }

    private void same(JSONObject actual, JSONObject expected) throws Exception {
        require(actual.getString("seed_hex").equals(expected.getString("seed_hex")), "Restored fixture secret");
        require(actual.getJSONObject("profile").getString("id").equals(expected.getJSONObject("profile").getString("id")), "Restored fixture identity");
        require(actual.getJSONArray("messages").getJSONObject(0).getString("text").equals("Hello 🌍 Welcome"), "Restored Unicode message");
    }

    @Override public void onStart() {
        Bundle report = new Bundle();
        try {
            Context context = getTargetContext();
            require(context.getPackageName().equals(PACKAGE), "Separate test package");
            require(!context.getFilesDir().getCanonicalPath().contains("/org.parano1d.courier/"), "Separate private storage");
            JSONObject expected = fixture();
            File archive = new File(context.getFilesDir(), "identity.pmc");
            File portable = new File(context.getFilesDir(), "fixture-backup.json");
            String stage = arguments.getString("stage", "create");
            if (stage.equals("create")) {
                new SecureStore(context).save(expected);
                same(new SecureStore(context).read(), expected);
                byte[] original = Files.readAllBytes(archive.toPath());
                require(!new String(original, StandardCharsets.ISO_8859_1).contains(SEED), "Local archive is encrypted");
                Files.write(new File(archive.getPath() + ".new").toPath(), new byte[]{1,2,3});
                same(new SecureStore(context).read(), expected);
                byte[] changed = original.clone(); changed[changed.length - 1] ^= 1;
                Files.write(archive.toPath(), changed);
                boolean rejected = false;
                try { new SecureStore(context).read(); } catch (Exception invalid) { rejected = true; }
                require(rejected, "Modified local archive rejected");

                String backup = result(new JSONObject().put("op", "backup_encrypt").put("data", expected.toString()).put("password", PASSWORD)).getString("backup");
                JSONObject restored = result(new JSONObject().put("op", "backup_decrypt").put("backup", backup).put("password", PASSWORD)).getJSONObject("data");
                same(restored, expected);
                require(!call(new JSONObject().put("op", "backup_decrypt").put("backup", backup).put("password", "wrong fixture password")).getBoolean("ok"), "Wrong backup password rejected");
                JSONObject changedBackup = new JSONObject(backup);
                String encrypted = changedBackup.getString("ciphertext");
                changedBackup.put("ciphertext", (encrypted.charAt(0) == '0' ? "1" : "0") + encrypted.substring(1));
                require(!call(new JSONObject().put("op", "backup_decrypt").put("backup", changedBackup.toString()).put("password", PASSWORD)).getBoolean("ok"), "Modified portable backup rejected");
                new SecureStore(context).save(restored);
                same(new SecureStore(context).read(), expected);
                Files.write(portable.toPath(), backup.getBytes(StandardCharsets.UTF_8));
            } else if (stage.equals("reopen")) {
                require(archive.isFile() && portable.isFile(), "Fixture survives process restart");
                same(new SecureStore(context).read(), expected);
                JSONObject restored = result(new JSONObject().put("op", "backup_decrypt").put("backup", new String(Files.readAllBytes(portable.toPath()), StandardCharsets.UTF_8)).put("password", PASSWORD)).getJSONObject("data");
                same(restored, expected);
            } else throw new IllegalArgumentException("Unknown check stage");
            report.putString("status", "passed"); report.putString("stage", stage); report.putInt("checks", checks);
            finish(Activity.RESULT_OK, report);
        } catch (Throwable error) {
            report.putString("status", "failed"); report.putString("error", error.getClass().getSimpleName() + ": " + error.getMessage());
            finish(Activity.RESULT_CANCELED, report);
        }
    }
}
