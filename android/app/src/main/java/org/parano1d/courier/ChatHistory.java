package org.parano1d.courier;

import org.json.JSONArray;
import org.json.JSONObject;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class ChatHistory {
    static final int MAX_MESSAGES = 5000;
    private static final int MAX_CLEARED = 20000;
    private static final long LIFETIME_MS = 7L * 24 * 60 * 60 * 1000;
    private static final String COMMUNITY = "g:parano1d";

    private static JSONArray array(JSONObject data, String key) {
        JSONArray value = data.optJSONArray(key);
        return value == null ? new JSONArray() : value;
    }

    private static boolean validChat(String chat) {
        return COMMUNITY.equals(chat) || chat.matches("d:[0-9a-f]{64}");
    }

    private static Set<String> queued(JSONObject data) throws Exception {
        Set<String> result = new HashSet<>();
        JSONArray outbox = array(data, "outbox");
        for (int i = 0; i < outbox.length(); i++) result.add(outbox.getJSONObject(i).getString("id"));
        return result;
    }

    private static long bytes(JSONObject value) {
        return value.toString().getBytes(StandardCharsets.UTF_8).length;
    }

    static JSONObject summary(JSONObject data, long usedBytes, long byteLimit) throws Exception {
        Set<String> queued = queued(data);
        Map<String, String> names = new HashMap<>();
        JSONArray contacts = array(data, "contacts");
        for (int i = 0; i < contacts.length(); i++) {
            JSONObject contact = contacts.getJSONObject(i);
            names.put("d:" + contact.getString("id"), contact.optString("name", "Private chat"));
        }
        Map<String, JSONObject> chats = new LinkedHashMap<>();
        chats.put(COMMUNITY, usage(COMMUNITY, "Community"));
        Map<String, String> scopes = new HashMap<>();
        JSONArray messages = array(data, "messages");
        for (int i = 0; i < messages.length(); i++) {
            JSONObject message = messages.getJSONObject(i);
            String scope = message.optString("chat"), id = message.getString("id");
            if (!validChat(scope)) continue;
            String name = names.get(scope);
            if (name == null && message.optJSONObject("sender") != null && scope.equals("d:" + message.getJSONObject("sender").optString("id"))) name = message.getJSONObject("sender").optString("name");
            JSONObject chat = chats.get(scope);
            if (chat == null) { chat = usage(scope, name == null || name.isEmpty() ? "Private chat" : name); chats.put(scope, chat); }
            chat.put("messages", chat.getInt("messages") + 1).put("bytes", chat.getLong("bytes") + bytes(message));
            if (queued.contains(id)) chat.put("queued", chat.getInt("queued") + 1);
            else chat.put("clearable", chat.getInt("clearable") + 1).put("clearable_bytes", chat.getLong("clearable_bytes") + bytes(message));
            scopes.put(id, scope);
        }
        JSONArray envelopes = array(data, "envelopes");
        for (int i = 0; i < envelopes.length(); i++) {
            JSONObject envelope = envelopes.getJSONObject(i); String id = envelope.getString("id");
            JSONObject chat = chats.get(scopes.get(id));
            if (chat == null) continue;
            chat.put("bytes", chat.getLong("bytes") + bytes(envelope));
            if (!queued.contains(id)) chat.put("clearable_bytes", chat.getLong("clearable_bytes") + bytes(envelope));
        }
        return new JSONObject().put("used_bytes", usedBytes).put("byte_limit", byteLimit)
            .put("messages", messages.length()).put("message_limit", MAX_MESSAGES)
            .put("full", data.optBoolean("storage_full") || messages.length() >= MAX_MESSAGES || usedBytes >= byteLimit)
            .put("chats", new JSONArray(chats.values()));
    }

    private static JSONObject usage(String id, String name) throws Exception {
        return new JSONObject().put("id", id).put("name", name).put("messages", 0).put("queued", 0)
            .put("clearable", 0).put("bytes", 0L).put("clearable_bytes", 0L);
    }

    static Set<String> clearedIds(JSONObject data, long now) {
        Set<String> result = new HashSet<>();
        JSONObject cleared = data.optJSONObject("cleared_messages");
        if (cleared != null) for (Iterator<String> it = cleared.keys(); it.hasNext();) {
            String id = it.next(); if (cleared.optLong(id) > now) result.add(id);
        }
        return result;
    }

    static boolean wasCleared(JSONObject data, String id, long now) {
        JSONObject cleared = data.optJSONObject("cleared_messages");
        return cleared != null && cleared.optLong(id) > now;
    }

    static void apply(JSONObject data, JSONObject cleared) throws Exception {
        for (String key : new String[]{"messages", "envelopes", "cleared_messages", "read_messages", "drafts", "contacts", "storage_full"}) {
            if (cleared.has(key)) data.put(key, cleared.get(key));
        }
    }

    static JSONObject clear(JSONObject original, JSONArray selected, long now) throws Exception {
        return clear(original, selected, now, true);
    }

    static JSONObject deleteConversation(JSONObject original, String chat, long now) throws Exception {
        if (!chat.matches("d:[0-9a-f]{64}")) throw new Exception("Choose a private conversation.");
        boolean found = false;
        JSONArray contacts = array(original, "contacts");
        for (int i = 0; i < contacts.length(); i++) if (chat.equals("d:" + contacts.getJSONObject(i).optString("id"))) { found = true; break; }
        if (!found) throw new Exception("Choose a private conversation.");
        JSONObject next = clear(original, new JSONArray().put(chat), now, false);
        JSONArray kept = new JSONArray();
        for (int i = 0; i < contacts.length(); i++) if (!chat.equals("d:" + contacts.getJSONObject(i).optString("id"))) kept.put(new JSONObject(contacts.getJSONObject(i).toString()));
        next.put("contacts", kept);
        JSONObject drafts = next.optJSONObject("drafts");
        if (drafts != null) drafts.remove(chat);
        return next;
    }

    private static JSONObject clear(JSONObject original, JSONArray selected, long now, boolean preserveQueued) throws Exception {
        if (selected == null || selected.length() == 0 || selected.length() > MAX_MESSAGES + 1) throw new Exception("Choose the chats to clear.");
        Set<String> chats = new HashSet<>();
        for (int i = 0; i < selected.length(); i++) {
            String chat = selected.getString(i);
            if (!validChat(chat)) throw new Exception("Choose a Community or private chat.");
            chats.add(chat);
        }
        JSONObject data = new JSONObject(original.toString());
        Set<String> queued = queued(data), removed = new HashSet<>();
        JSONArray messages = array(data, "messages"), kept = new JSONArray();
        Map<String, Long> cleared = new HashMap<>();
        JSONObject previous = data.optJSONObject("cleared_messages");
        if (previous != null) for (Iterator<String> it = previous.keys(); it.hasNext();) {
            String id = it.next(); long until = previous.optLong(id); if (until > now) cleared.put(id, until);
        }
        for (int i = 0; i < messages.length(); i++) {
            JSONObject message = messages.getJSONObject(i); String id = message.getString("id");
            if (!chats.contains(message.optString("chat")) || preserveQueued && queued.contains(id)) { kept.put(message); continue; }
            removed.add(id);
            long created = message.optLong("created_ms", now);
            long until = Math.min(now, Math.max(0, created)) + LIFETIME_MS;
            if (until > now) cleared.put(id, until);
        }
        JSONArray envelopes = array(data, "envelopes"), retained = new JSONArray();
        for (int i = 0; i < envelopes.length(); i++) {
            JSONObject envelope = envelopes.getJSONObject(i); String id = envelope.getString("id");
            if (!removed.contains(id)) retained.put(envelope);
            else if (envelope.optJSONObject("data") != null) {
                long until = Math.min(now + LIFETIME_MS, envelope.getJSONObject("data").optLong("expires_ms"));
                if (until > now) cleared.put(id, Math.max(cleared.getOrDefault(id, 0L), until));
            }
        }
        List<Map.Entry<String, Long>> entries = new ArrayList<>(cleared.entrySet());
        entries.sort((a, b) -> Long.compare(b.getValue(), a.getValue()));
        JSONObject markers = new JSONObject();
        for (int i = 0; i < Math.min(MAX_CLEARED, entries.size()); i++) markers.put(entries.get(i).getKey(), entries.get(i).getValue());
        JSONObject read = data.optJSONObject("read_messages"), drafts = data.optJSONObject("drafts");
        for (String chat : chats) {
            if (read != null) read.remove(chat);
            JSONObject draft = drafts == null ? null : drafts.optJSONObject(chat);
            if (draft != null && removed.contains(draft.optString("reply_to"))) draft.put("reply_to", "");
        }
        return data.put("messages", kept).put("envelopes", retained).put("cleared_messages", markers).put("storage_full", false);
    }
}
