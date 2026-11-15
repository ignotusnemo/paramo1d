package org.parano1d.courier;

import org.json.JSONArray;
import org.json.JSONObject;
import org.junit.Test;
import static org.junit.Assert.*;

public final class ChatPolicyTest {
    private JSONObject envelope(String type) throws Exception {
        return new JSONObject().put("data",new JSONObject().put("destination",new JSONObject().put("type",type)));
    }
    @Test public void publicBacklogDoesNotBlockPrivateDelivery() throws Exception {
        JSONArray source=new JSONArray();
        for(int i=0;i<12;i++)source.put(envelope("group"));
        JSONObject direct=envelope("direct");source.put(direct);
        JSONArray allowed=ChatPolicy.envelopes(source,true);
        assertEquals(1,allowed.length());assertSame(direct,allowed.getJSONObject(0));
        assertEquals(13,source.length());assertSame(source,ChatPolicy.envelopes(source,false));
    }
    @Test public void modeHidesPublicHistoryAndKeepsItForRestoration() throws Exception {
        JSONArray source=new JSONArray().put(new JSONObject().put("chat","g:parano1d"))
            .put(new JSONObject().put("chat","d:contact"));
        assertEquals(1,ChatPolicy.messages(source,true).length());
        assertEquals(2,ChatPolicy.messages(source,false).length());
        assertEquals(2,source.length());
    }
    @Test public void groupAndMalformedEnvelopesAreExcluded() throws Exception {
        assertFalse(ChatPolicy.allows(envelope("group"),true));
        assertFalse(ChatPolicy.allows(new JSONObject(),true));
        assertTrue(ChatPolicy.allows(envelope("direct"),true));
        assertTrue(ChatPolicy.allows(envelope("group"),false));
    }
}
