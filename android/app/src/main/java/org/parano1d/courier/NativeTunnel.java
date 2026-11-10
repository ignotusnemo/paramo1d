package org.parano1d.courier;

/** The tunnel owns a userspace network stack. It registers no Android VpnService. */
final class NativeTunnel {
    static { System.loadLibrary("paramo1d_tunnel"); }
    static native String call(String request);
}
