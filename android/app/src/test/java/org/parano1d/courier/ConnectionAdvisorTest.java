package org.parano1d.courier;

import org.junit.Test;
import static org.junit.Assert.*;

public final class ConnectionAdvisorTest {
    @Test public void aStalledRequestCanPromptBeforeReturningAnError() {
        ConnectionAdvisor a = new ConnectionAdvisor();
        a.walletWaiting(30000,14999);
        assertEquals("",a.recommendation(30000,true,false,false));
        a.walletWaiting(30001,15000);
        assertEquals("wallet",a.recommendation(30001,true,false,false));
        assertEquals("",a.recommendation(30001,true,true,false));
        a.walletWaiting(31000,100);
        assertEquals("",a.issue(31000));
        a.walletWaiting(50000,16000);
        a.walletConnected();
        assertEquals("",a.issue(50000));
    }
    @Test public void transientFailuresDoNotPromptAndSustainedFailuresDo() {
        ConnectionAdvisor a = new ConnectionAdvisor();
        a.chatFailed(1000);a.chatFailed(5000);
        assertEquals("",a.recommendation(20000,true,false,false));
        a.chatFailed(9000);
        assertEquals("",a.recommendation(10000,true,false,false));
        assertEquals("chat",a.recommendation(11000,true,false,false));
    }
    @Test public void offlineNearbyAndEnabledVpnDoNotPrompt() {
        ConnectionAdvisor a = new ConnectionAdvisor();
        a.walletFailed(0);a.walletFailed(10000);
        assertEquals("",a.recommendation(12000,false,false,false));
        assertEquals("",a.recommendation(12000,true,false,true));
        assertEquals("",a.recommendation(12000,true,true,false));
        assertEquals("wallet",a.recommendation(12000,true,false,false));
    }
    @Test public void successResetsOnlyTheAffectedChannel() {
        ConnectionAdvisor a = new ConnectionAdvisor();
        a.chatFailed(0);a.chatFailed(4000);a.chatFailed(10000);
        a.walletFailed(0);a.walletFailed(10000);
        a.chatConnected();
        assertEquals("wallet",a.recommendation(12000,true,false,false));
        a.walletConnected();assertEquals("",a.issue(12000));
    }
    @Test public void dismissalSurvivesNewEpisodesAndCanBeRestored() {
        ConnectionAdvisor a = new ConnectionAdvisor();
        a.walletFailed(0);a.walletFailed(10000);a.shown(12000);
        assertEquals("",a.recommendation(12001,true,false,false));
        a.walletConnected();a.walletFailed(14000);a.walletFailed(30000);
        assertEquals("",a.recommendation(30000,true,false,false));
        assertEquals("wallet",a.recommendation(12000+ConnectionAdvisor.COOLDOWN_MS,true,false,false));
        ConnectionAdvisor restored = new ConnectionAdvisor();restored.suppressUntil(40000);
        restored.walletFailed(0);restored.walletFailed(10000);
        assertEquals("",restored.recommendation(30000,true,false,false));
    }
}
