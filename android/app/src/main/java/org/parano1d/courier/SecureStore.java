package org.parano1d.courier;

import android.content.Context;
import android.security.keystore.KeyGenParameterSpec;
import android.security.keystore.KeyProperties;
import android.util.AtomicFile;
import org.json.JSONObject;
import java.io.File;
import java.io.FileOutputStream;
import java.nio.charset.StandardCharsets;
import java.security.KeyStore;
import java.util.Arrays;
import javax.crypto.Cipher;
import javax.crypto.KeyGenerator;
import javax.crypto.SecretKey;
import javax.crypto.spec.GCMParameterSpec;

final class SecureStore {
    private static final String ALIAS = "paramo1d-local-store-v1";
    private static final byte[] AAD = "Paramo1d/local-store/1".getBytes(StandardCharsets.UTF_8);
    private static final int MAX_BYTES = 32 * 1024 * 1024;
    static final int ADMISSION_BYTES = 24 * 1024 * 1024;
    private final AtomicFile file;
    private int savedBytes;
    private long reservedBytes;
    static final class Full extends Exception { Full() { super("App storage is full. Open Settings to clear local chat history."); } }
    void reserveRoom(int bytes) throws Full {
        if (bytes <= 0) return;
        if ((long)savedBytes + reservedBytes + bytes > ADMISSION_BYTES) throw new Full();
        reservedBytes += bytes;
    }
    SecureStore(Context context) { file = new AtomicFile(new File(context.getFilesDir(), "identity.pmc")); }
    int savedBytes() { return savedBytes; }
    boolean isFull() { return (long)savedBytes + reservedBytes >= ADMISSION_BYTES; }
    private SecretKey key() throws Exception {
        KeyStore store = KeyStore.getInstance("AndroidKeyStore"); store.load(null);
        if (!store.containsAlias(ALIAS)) {
            KeyGenerator generator = KeyGenerator.getInstance(KeyProperties.KEY_ALGORITHM_AES, "AndroidKeyStore");
            generator.init(new KeyGenParameterSpec.Builder(ALIAS, KeyProperties.PURPOSE_ENCRYPT | KeyProperties.PURPOSE_DECRYPT)
                .setKeySize(256).setBlockModes(KeyProperties.BLOCK_MODE_GCM)
                .setEncryptionPaddings(KeyProperties.ENCRYPTION_PADDING_NONE).build());
            generator.generateKey();
        }
        return (SecretKey) store.getKey(ALIAS, null);
    }
    JSONObject read() throws Exception {
        if (!file.getBaseFile().exists()) return new JSONObject();
        if (file.getBaseFile().length() > MAX_BYTES) throw new Exception("Local identity file exceeds size limit");
        byte[] bytes = file.readFully();
        if (bytes.length < 29 || bytes.length > MAX_BYTES) throw new Exception("Local identity file is invalid");
        Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
        cipher.init(Cipher.DECRYPT_MODE, key(), new GCMParameterSpec(128, Arrays.copyOfRange(bytes, 0, 12)));
        cipher.updateAAD(AAD);
        byte[] plain = cipher.doFinal(bytes, 12, bytes.length - 12);
        savedBytes = plain.length; reservedBytes = 0;
        try { return new JSONObject(new String(plain, StandardCharsets.UTF_8)); }
        finally { Arrays.fill(plain, (byte) 0); }
    }
    void save(JSONObject state) throws Exception {
        byte[] plain = state.toString().getBytes(StandardCharsets.UTF_8);
        int encodedBytes = plain.length;
        if (plain.length > MAX_BYTES - 64) throw new Exception("Local storage is full; export a backup");
        Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding"); cipher.init(Cipher.ENCRYPT_MODE, key()); cipher.updateAAD(AAD);
        byte[] encrypted;
        try { encrypted = cipher.doFinal(plain); } finally { Arrays.fill(plain, (byte) 0); }
        FileOutputStream stream = null;
        try { stream = file.startWrite(); stream.write(cipher.getIV()); stream.write(encrypted); file.finishWrite(stream); savedBytes = encodedBytes; reservedBytes = 0; }
        catch (Exception error) { if (stream != null) file.failWrite(stream); throw error; }
    }
}
