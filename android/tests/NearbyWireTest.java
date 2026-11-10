package org.parano1d.courier;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;

public final class NearbyWireTest {
    public static void main(String[] args) throws Exception {
        ByteArrayOutputStream wire = new ByteArrayOutputStream();
        byte[][] frames = {"hello".getBytes(java.nio.charset.StandardCharsets.UTF_8), new byte[4000], new byte[NearbyWire.MAX_FRAME]};
        frames[2][frames[2].length - 1] = 71;
        for (byte[] frame : frames) NearbyWire.write(wire, frame);
        byte[] encoded = wire.toByteArray();
        InputStream fragmented = new ByteArrayInputStream(encoded) { @Override public synchronized int read(byte[] bytes, int offset, int length) { return super.read(bytes, offset, Math.min(length, 3)); } };
        for (byte[] frame : frames) if (!Arrays.equals(frame, NearbyWire.read(fragmented))) throw new AssertionError("Fragmented nearby transfer changed bytes");
        for (int bad : new int[]{0, -1, NearbyWire.MAX_FRAME + 1, Integer.MAX_VALUE}) {
            ByteArrayOutputStream bytes = new ByteArrayOutputStream(); new DataOutputStream(bytes).writeInt(bad);
            try { NearbyWire.read(new ByteArrayInputStream(bytes.toByteArray())); throw new AssertionError("Invalid length accepted"); } catch (IOException expected) { }
        }
        try {
            InputStream truncated = new ByteArrayInputStream(Arrays.copyOf(encoded, encoded.length - 1));
            for (int i = 0; i < frames.length; i++) NearbyWire.read(truncated);
            throw new AssertionError("Truncated final frame accepted");
        } catch (IOException expected) { }
        System.out.println("PASS: nearby framing preserves fragmented streams and rejects oversized, negative and truncated frames.");
    }
}
