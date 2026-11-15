package org.parano1d.courier;

import org.json.JSONArray;
import org.json.JSONObject;

final class ChatPolicy {
    static boolean allows(JSONObject envelope, boolean paranoid) {
        JSONObject body = envelope.optJSONObject("data");
        JSONObject destination = body == null ? null : body.optJSONObject("destination");
        return !paranoid || destination != null && "direct".equals(destination.optString("type"));
    }
    static JSONArray envelopes(JSONArray source, boolean paranoid) {
        if (!paranoid) return source;
        JSONArray visible = new JSONArray();
        for (int i=0;i<source.length();i++) {
            JSONObject item=source.optJSONObject(i);
            if(item!=null && allows(item,true)) visible.put(item);
        }
        return visible;
    }
    static JSONArray messages(JSONArray source, boolean paranoid) {
        if (!paranoid) return source;
        JSONArray visible = new JSONArray();
        for (int i=0;i<source.length();i++) {
            JSONObject item=source.optJSONObject(i);
            if(item!=null && item.optString("chat").startsWith("d:")) visible.put(item);
        }
        return visible;
    }
}
