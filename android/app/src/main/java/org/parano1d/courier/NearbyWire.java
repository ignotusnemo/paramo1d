package org.parano1d.courier;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

/** Length-delimited frames shared by nearby transports. */
final class NearbyWire {
    static final int MAX_FRAME = 1024 * 1024 + 8192;
    static byte[] read(InputStream input) throws IOException {
        DataInputStream stream = new DataInputStream(input);
        int length = stream.readInt();
        if (length < 1 || length > MAX_FRAME) throw new IOException("Nearby packet exceeds limit");
        byte[] bytes = new byte[length]; stream.readFully(bytes); return bytes;
    }
    static void write(OutputStream output, byte[] bytes) throws IOException {
        if (bytes.length < 1 || bytes.length > MAX_FRAME) throw new IOException("Nearby packet exceeds limit");
        DataOutputStream stream = new DataOutputStream(output); stream.writeInt(bytes.length); stream.write(bytes); stream.flush();
    }
}
