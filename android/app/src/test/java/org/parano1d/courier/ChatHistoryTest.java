package org.parano1d.courier;

import org.json.JSONArray;
import org.json.JSONObject;
import org.junit.Test;
import java.util.Set;
import static org.junit.Assert.*;

public class ChatHistoryTest {
    private static final long NOW = 1800000000000L;
    private static final String GROUP = "g:parano1d";
    private static final String BOB = "d:" + "22".repeat(32), EVE = "d:" + "33".repeat(32);

    private JSONObject message(String id, String chat) throws Exception {
        return new JSONObject().put("id", id).put("chat", chat).put("created_ms", NOW - 1000)
            .put("message", new JSONObject().put("type", "text").put("text", "Hello 🌍"));
    }
    private JSONObject envelope(String id) throws Exception {
        return new JSONObject().put("id", id).put("data", new JSONObject().put("expires_ms", NOW + 60000)).put("ciphertext", "opaque");
    }
    private JSONObject fixture() throws Exception {
        JSONObject data = new JSONObject();
        data.put("seed_hex", "fixture identity").put("profile", new JSONObject().put("id", "11".repeat(32)));
        data.put("contacts", new JSONArray().put(new JSONObject().put("id", "22".repeat(32)).put("name", "Bob")).put(new JSONObject().put("id", "33".repeat(32)).put("name", "Eve")));
        data.put("messages", new JSONArray().put(message("g1", GROUP)).put(message("g2", GROUP)).put(message("queued", GROUP)).put(message("b1", BOB)).put(message("e1", EVE)));
        data.put("outbox", new JSONArray().put(envelope("queued")));
        data.put("envelopes", new JSONArray().put(envelope("g1")).put(envelope("queued")).put(envelope("b1")).put(envelope("opaque-for-another-person")));
        data.put("receipts", new JSONArray().put(new JSONObject().put("txid", "paid").put("verified", true).put("receipt_hex", "receipt")));
        data.put("prepared_payments", new JSONArray().put(new JSONObject().put("txid", "pending").put("intent_hex", "authorization")));
        data.put("observations", new JSONArray().put(new JSONObject().put("id", "report").put("message", new JSONObject().put("txid", "pending").put("stage", "mempool"))));
        data.put("watches", new JSONArray().put(new JSONObject().put("txid", "pending")));
        data.put("chain", new JSONObject().put("verified", true).put("balance", "1.23"));
        data.put("cursors", new JSONObject().put("relay|g:parano1d", 75).put("relay|inbox", 40));
        data.put("read_messages", new JSONObject().put(GROUP, "g2").put(BOB, "b1").put(EVE, "e1"));
        data.put("drafts", new JSONObject().put(GROUP, new JSONObject().put("text", "Unsent draft").put("reply_to", "g1")).put(BOB, new JSONObject().put("text", "Bob draft")));
        return data.put("storage_full", true);
    }
    private Set<String> ids(JSONObject data, String key) throws Exception {
        Set<String> ids = new java.util.HashSet<>(); JSONArray items = data.getJSONArray(key);
        for (int i = 0; i < items.length(); i++) ids.add(items.getJSONObject(i).getString("id"));
        return ids;
    }

    @Test public void communityCleanupPreservesOtherChatsAndFinancialState() throws Exception {
        JSONObject before = fixture(), next = ChatHistory.clear(before, new JSONArray().put(GROUP), NOW);
        assertEquals(Set.of("queued", "b1", "e1"), ids(next, "messages"));
        assertEquals(Set.of("queued", "b1", "opaque-for-another-person"), ids(next, "envelopes"));
        for (String key : new String[]{"seed_hex", "profile", "contacts", "outbox", "receipts", "prepared_payments", "observations", "watches", "chain", "cursors"}) assertEquals(key, before.get(key).toString(), next.get(key).toString());
        assertFalse(next.getJSONObject("read_messages").has(GROUP));
        assertEquals("b1", next.getJSONObject("read_messages").getString(BOB));
        assertEquals("Unsent draft", next.getJSONObject("drafts").getJSONObject(GROUP).getString("text"));
        assertEquals("", next.getJSONObject("drafts").getJSONObject(GROUP).getString("reply_to"));
        assertEquals("Bob draft", next.getJSONObject("drafts").getJSONObject(BOB).getString("text"));
        assertFalse(next.getBoolean("storage_full"));
        assertEquals(5, before.getJSONArray("messages").length());
    }
    @Test public void onlyTheSelectedPrivateChatIsCleared() throws Exception {
        JSONObject next = ChatHistory.clear(fixture(), new JSONArray().put(BOB), NOW);
        assertEquals(Set.of("g1", "g2", "queued", "e1"), ids(next, "messages"));
        assertFalse(next.getJSONObject("read_messages").has(BOB));
        assertEquals("g2", next.getJSONObject("read_messages").getString(GROUP));
        assertEquals(2, next.getJSONArray("contacts").length());
    }
    @Test public void multipleSelectionsKeepQueuedMessages() throws Exception {
        JSONObject next = ChatHistory.clear(fixture(), new JSONArray().put(GROUP).put(BOB).put(EVE).put(GROUP), NOW);
        assertEquals(Set.of("queued"), ids(next, "messages"));
        assertEquals(Set.of("queued"), ids(next, "outbox"));
        assertEquals(1, next.getJSONArray("receipts").length());
    }
    @Test public void invalidSelectionsLeaveTheOriginalUntouched() throws Exception {
        for (JSONArray choice : new JSONArray[]{new JSONArray(), new JSONArray().put(GROUP).put("g:unknown"), new JSONArray().put("d:bad")}) {
            JSONObject data = fixture(); String before = data.toString();
            try { ChatHistory.clear(data, choice, NOW); fail("Invalid chat selection accepted"); }
            catch (Exception expected) { assertEquals(before, data.toString()); }
        }
    }
    @Test public void storageSummarySeparatesCommunityPrivateAndQueuedMessages() throws Exception {
        JSONObject summary = ChatHistory.summary(fixture(), 4096, 8192); JSONArray chats = summary.getJSONArray("chats");
        assertEquals(5, summary.getInt("messages")); assertTrue(summary.getBoolean("full"));
        assertEquals(3, chats.length());
        JSONObject group = chats.getJSONObject(0);
        assertEquals(GROUP, group.getString("id")); assertEquals(3, group.getInt("messages"));
        assertEquals(2, group.getInt("clearable")); assertEquals(1, group.getInt("queued"));
        assertTrue(group.getLong("bytes") > group.getLong("clearable_bytes"));
        assertEquals("Bob", chats.getJSONObject(1).getString("name"));
    }
    @Test public void clearedMessagesAreRecognizedUntilTheirDeliveryLifetimeEnds() throws Exception {
        JSONObject next = ChatHistory.clear(fixture(), new JSONArray().put(GROUP), NOW);
        assertTrue(ChatHistory.wasCleared(next, "g1", NOW));
        assertTrue(ChatHistory.clearedIds(next, NOW).contains("g2"));
        assertFalse(ChatHistory.wasCleared(next, "queued", NOW));
        assertFalse(ChatHistory.wasCleared(next, "a-new-message", NOW));
        assertFalse(ChatHistory.wasCleared(next, "g1", NOW + 7L * 24 * 60 * 60 * 1000));
    }
    @Test public void expiredHistoryDoesNotGrowTheReplayCache() throws Exception {
        JSONObject data = fixture();
        data.getJSONArray("messages").getJSONObject(0).put("created_ms", NOW - 8L * 24 * 60 * 60 * 1000);
        data.getJSONArray("envelopes").getJSONObject(0).getJSONObject("data").put("expires_ms", NOW - 1);
        data.put("cleared_messages", new JSONObject().put("expired-marker", NOW - 1));
        JSONObject next = ChatHistory.clear(data, new JSONArray().put(GROUP), NOW);
        assertFalse(next.getJSONObject("cleared_messages").has("g1"));
        assertFalse(next.getJSONObject("cleared_messages").has("expired-marker"));
    }
    @Test public void replayCacheIsBoundedAndKeepsRecentCleanup() throws Exception {
        JSONObject data = fixture(), cleared = new JSONObject();
        for (int i = 0; i < 20010; i++) cleared.put("old-" + i, NOW + 1000 + i);
        data.put("cleared_messages", cleared);
        JSONObject next = ChatHistory.clear(data, new JSONArray().put(GROUP), NOW);
        assertEquals(20000, next.getJSONObject("cleared_messages").length());
        assertTrue(ChatHistory.wasCleared(next, "g1", NOW));
    }
    @Test public void cleanupIsIdempotentAndKeepsUnsentDrafts() throws Exception {
        JSONObject first = ChatHistory.clear(fixture(), new JSONArray().put(BOB), NOW);
        JSONObject second = ChatHistory.clear(first, new JSONArray().put(BOB), NOW);
        assertEquals(ids(first, "messages"), ids(second, "messages"));
        assertEquals(first.getJSONObject("drafts").toString(), second.getJSONObject("drafts").toString());
    }
    @Test public void anEmptyArchiveStillOffersTheCommunityScope() throws Exception {
        JSONObject summary = ChatHistory.summary(new JSONObject(), 0, 8192);
        assertEquals(1, summary.getJSONArray("chats").length());
        assertEquals(0, summary.getJSONArray("chats").getJSONObject(0).getInt("clearable"));
        assertFalse(summary.getBoolean("full"));
    }
    @Test public void applyingCleanupKeepsLiveWalletAndDeliveryReferences() throws Exception {
        JSONObject data = fixture(), chain = data.getJSONObject("chain");
        JSONArray payments = data.getJSONArray("prepared_payments"), outbox = data.getJSONArray("outbox"), receipts = data.getJSONArray("receipts");
        JSONObject next = ChatHistory.clear(data, new JSONArray().put(GROUP), NOW);
        ChatHistory.apply(data, next);
        assertSame(chain, data.getJSONObject("chain")); assertSame(payments, data.getJSONArray("prepared_payments"));
        assertSame(outbox, data.getJSONArray("outbox")); assertSame(receipts, data.getJSONArray("receipts"));
        chain.put("balance", "2.34"); payments.put(new JSONObject().put("txid", "just-authorized"));
        assertEquals("2.34", data.getJSONObject("chain").getString("balance"));
        assertEquals(2, data.getJSONArray("prepared_payments").length());
        assertEquals(Set.of("queued", "b1", "e1"), ids(data, "messages"));
    }
    @Test public void deletingPrivateChatRemovesItsContactDraftAndCompleteHistory() throws Exception {
        JSONObject data = fixture();
        data.getJSONArray("messages").put(message("queued-private", BOB));
        data.getJSONArray("outbox").put(envelope("queued-private"));
        data.getJSONArray("envelopes").put(envelope("queued-private"));
        String original = data.toString();
        JSONObject next = ChatHistory.deleteConversation(data, BOB, NOW);
        assertEquals(Set.of("g1", "g2", "queued", "e1"), ids(next, "messages"));
        assertEquals(Set.of("g1", "queued", "opaque-for-another-person"), ids(next, "envelopes"));
        assertEquals(1, next.getJSONArray("contacts").length());
        assertEquals("33".repeat(32), next.getJSONArray("contacts").getJSONObject(0).getString("id"));
        assertFalse(next.getJSONObject("drafts").has(BOB));
        assertFalse(next.getJSONObject("read_messages").has(BOB));
        for (String key : new String[]{"seed_hex", "profile", "outbox", "receipts", "prepared_payments", "observations", "watches", "chain", "cursors"}) assertEquals(key, data.get(key).toString(), next.get(key).toString());
        assertEquals(original, data.toString());
    }
    @Test public void deletionRejectsCommunityMalformedAndUnknownContacts() throws Exception {
        for (String scope : new String[]{GROUP, "d:bad", "d:" + "44".repeat(32)}) {
            JSONObject data = fixture(); String before = data.toString();
            try { ChatHistory.deleteConversation(data, scope, NOW); fail("Invalid private chat accepted"); }
            catch (Exception expected) { assertEquals(before, data.toString()); }
        }
    }
    @Test public void deletedHistoryStaysDeletedAcrossReloadAndNewMessagesCanArrive() throws Exception {
        JSONObject data = new JSONObject(ChatHistory.deleteConversation(fixture(), BOB, NOW).toString());
        assertTrue(ChatHistory.wasCleared(data, "b1", NOW));
        assertFalse(ChatHistory.wasCleared(data, "new-bob-message", NOW));
        data.getJSONArray("contacts").put(new JSONObject().put("id", "22".repeat(32)).put("name", "Bob"));
        data.getJSONArray("messages").put(message("new-bob-message", BOB));
        assertEquals(Set.of("g1", "g2", "queued", "e1", "new-bob-message"), ids(data, "messages"));
        assertEquals(2, data.getJSONArray("contacts").length());
        assertFalse(data.getJSONObject("drafts").has(BOB));
    }
    @Test public void applyingDeletionPreservesLiveFinancialReferences() throws Exception {
        JSONObject data = fixture(), chain = data.getJSONObject("chain");
        JSONArray outbox = data.getJSONArray("outbox"), payments = data.getJSONArray("prepared_payments");
        ChatHistory.apply(data, ChatHistory.deleteConversation(data, BOB, NOW));
        assertSame(chain, data.getJSONObject("chain"));
        assertSame(outbox, data.getJSONArray("outbox"));
        assertSame(payments, data.getJSONArray("prepared_payments"));
        assertEquals(1, data.getJSONArray("contacts").length());
        assertFalse(ids(data, "messages").contains("b1"));
    }
}
