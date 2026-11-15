package org.parano1d.courier;

/** Offers an optional protected route after stalled or failed connections. */
final class ConnectionAdvisor {
    static final long MIN_FAILURE_MS = 10_000;
    static final long MIN_NETWORK_WAIT_MS = 15_000;
    static final long COOLDOWN_MS = 60 * 60 * 1000;
    private final Lane chat = new Lane();
    private final Lane wallet = new Lane();
    private long suppressedUntil;
    private long walletWaitSince;

    private static final class Lane {
        int failures;
        long since;
        void fail(long now) { if (failures == 0) since = now; failures++; }
        void clear() { failures = 0; since = 0; }
        boolean ready(long now, int required) { return failures >= required && now - since >= MIN_FAILURE_MS; }
    }

    void chatFailed(long now) { chat.fail(now); }
    void walletFailed(long now) { wallet.fail(now); }
    void chatConnected() { chat.clear(); }
    void walletConnected() { wallet.clear(); walletWaitSince = 0; }
    void walletWaiting(long now, long idleMs) { walletWaitSince = idleMs >= MIN_NETWORK_WAIT_MS ? Math.max(1, now - idleMs) : 0; }
    void suppressUntil(long until) { suppressedUntil = Math.max(suppressedUntil, until); }
    void shown(long now) { suppressUntil(now + COOLDOWN_MS); }

    String issue(long now) {
        if (chat.ready(now, 3)) return "chat";
        if (wallet.ready(now, 2) || walletWaitSince != 0) return "wallet";
        return "";
    }

    String recommendation(long now, boolean internet, boolean vpn, boolean nearby) {
        return !internet || vpn || nearby || now < suppressedUntil ? "" : issue(now);
    }

    String id(String issue) { return issue + ":" + (issue.equals("chat") ? chat.since : wallet.failures > 0 ? wallet.since : walletWaitSince); }
}
