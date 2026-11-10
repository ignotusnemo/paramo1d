package org.parano1d.courier;

final class NativeCore {
    static { System.loadLibrary("paramo1d"); }
    static native String call(String request);
}
