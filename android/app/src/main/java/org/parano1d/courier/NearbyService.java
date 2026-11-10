package org.parano1d.courier;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothClass;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothManager;
import android.bluetooth.BluetoothServerSocket;
import android.bluetooth.BluetoothSocket;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.os.IBinder;
import org.json.JSONArray;
import org.json.JSONObject;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.security.SecureRandom;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

/** Opt-in Bluetooth carriage for the same authenticated envelopes used by HTTPS relays. */
public final class NearbyService extends Service {
    static final String STOP = "org.parano1d.courier.STOP_NEARBY";
    private static final UUID PROTOCOL = UUID.fromString("d5a401c2-f826-4d99-966e-9a1d0d90e1d1");
    private static volatile NearbyService running;
    private final Map<String, Link> links = new ConcurrentHashMap<>();
    private final Map<String, BluetoothDevice> devices = new ConcurrentHashMap<>();
    private final ExecutorService io = new ThreadPoolExecutor(0, 4, 30, TimeUnit.SECONDS, new SynchronousQueue<>());
    private final ScheduledExecutorService timer = Executors.newSingleThreadScheduledExecutor();
    private BluetoothAdapter adapter;
    private BluetoothServerSocket server;
    private volatile boolean stopped, scanning;
    private volatile String problem = "";

    static JSONObject snapshot() {
        JSONObject state = new JSONObject(); JSONArray peers = new JSONArray(), found = new JSONArray();
        NearbyService service = running;
        try {
            if (service != null) {
                for (Link link : service.links.values()) if (link.contact != null && link.authenticated) peers.put(new JSONObject().put("id", link.contact.getString("id")).put("name", link.contact.getString("name")));
                for (BluetoothDevice device : service.devices.values()) found.put(new JSONObject().put("address", device.getAddress()).put("name", device.getName() == null ? "Nearby phone" : device.getName()));
            }
            state.put("enabled", service != null && !service.stopped).put("peers", peers).put("devices", found).put("scanning", service != null && service.scanning).put("problem", service == null ? "" : service.problem);
        } catch (Exception unavailable) { }
        return state;
    }
    static void offer(JSONObject envelope) {
        NearbyService service = running;
        if (service != null) service.broadcast(envelope, null);
    }
    static void scan() {
        NearbyService service = running;
        if (service == null) return;
        try { service.devices.clear(); for (BluetoothDevice device : service.adapter.getBondedDevices()) service.remember(device); service.scanning = service.adapter.startDiscovery(); service.updated(); }
        catch (Exception error) { service.problem = "Allow access to nearby devices to search."; service.updated(); }
    }
    static void connect(String address) throws Exception {
        NearbyService service = running; if (service == null) throw new Exception("Turn on Nearby first");
        if (!BluetoothAdapter.checkBluetoothAddress(address)) throw new Exception("Choose a nearby device");
        service.io.execute(() -> {
            BluetoothSocket socket = null;
            try {
                service.adapter.cancelDiscovery(); service.scanning = false;
                socket = service.adapter.getRemoteDevice(address).createInsecureRfcommSocketToServiceRecord(PROTOCOL);
                final BluetoothSocket waiting = socket;
                java.util.concurrent.ScheduledFuture<?> timeout = service.timer.schedule(() -> { try { waiting.close(); } catch (IOException ignored) { } }, 45, TimeUnit.SECONDS);
                try { socket.connect(); } finally { timeout.cancel(false); }
                service.attach(socket);
            } catch (Exception error) { if (socket != null) try { socket.close(); } catch (IOException ignored) { } service.problem = "Open Nearby in Paramo1d on the other device, then try again."; service.updated(); }
        });
    }
    private void remember(BluetoothDevice device) {
        try { BluetoothClass kind = device.getBluetoothClass(); int major = kind == null ? 0 : kind.getMajorDeviceClass();
            if (devices.size() < 40 && (major == 0 || major == BluetoothClass.Device.Major.PHONE || major == BluetoothClass.Device.Major.COMPUTER || major == BluetoothClass.Device.Major.UNCATEGORIZED)) devices.put(device.getAddress(), device);
        } catch (SecurityException ignored) { }
    }
    private final BroadcastReceiver discovery = new BroadcastReceiver() {
        @Override public void onReceive(Context context, Intent intent) {
            if (BluetoothDevice.ACTION_FOUND.equals(intent.getAction())) { BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE); if (device != null) remember(device); }
            if (BluetoothAdapter.ACTION_DISCOVERY_FINISHED.equals(intent.getAction())) scanning = false;
            if (BluetoothAdapter.ACTION_STATE_CHANGED.equals(intent.getAction()) && intent.getIntExtra(BluetoothAdapter.EXTRA_STATE, 0) == BluetoothAdapter.STATE_OFF) stopSelf();
            updated();
        }
    };
    @Override public void onCreate() {
        super.onCreate(); running = this;
        NotificationManager notifications = getSystemService(NotificationManager.class);
        notifications.createNotificationChannel(new NotificationChannel("nearby", "Nearby messaging", NotificationManager.IMPORTANCE_LOW));
        PendingIntent open = PendingIntent.getActivity(this, 0, new Intent(this, MainActivity.class), PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        PendingIntent stop = PendingIntent.getService(this, 0, new Intent(this, NearbyService.class).setAction(STOP), PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        Notification notification = new Notification.Builder(this, "nearby").setSmallIcon(org.parano1d.courier.R.drawable.ic_nearby).setContentTitle("Nearby messaging is on").setContentText("Carry messages to people and the network.").setContentIntent(open).setOngoing(true).addAction(new Notification.Action.Builder(null, "Turn off", stop).build()).build();
        startForeground(71, notification);
        try {
            adapter = getSystemService(BluetoothManager.class).getAdapter();
            if (adapter == null || !adapter.isEnabled()) throw new IOException("Turn on Bluetooth to use Nearby");
            IntentFilter filter = new IntentFilter(BluetoothDevice.ACTION_FOUND); filter.addAction(BluetoothAdapter.ACTION_DISCOVERY_FINISHED); filter.addAction(BluetoothAdapter.ACTION_STATE_CHANGED);
            if (android.os.Build.VERSION.SDK_INT >= 33) registerReceiver(discovery, filter, Context.RECEIVER_EXPORTED); else registerReceiver(discovery, filter);
            server = adapter.listenUsingInsecureRfcommWithServiceRecord("Paramo1d nearby", PROTOCOL);
            io.execute(() -> { while (!stopped) { try { BluetoothSocket socket = server.accept(); if (links.size() >= 2) socket.close(); else attach(socket); } catch (Exception error) { if (!stopped) { problem = "Nearby connection interrupted. Turn Nearby off and on to retry."; updated(); } break; } } });
            timer.scheduleWithFixedDelay(() -> { if (!stopped) { for (Link link : links.values()) if (link.authenticated) link.inventory(); MainActivity.nearbyCall("poll", new JSONObject()); } }, 2, 15, TimeUnit.SECONDS);
        } catch (Exception error) { problem = error.getMessage() == null ? "Nearby could not start" : error.getMessage(); stopSelf(); }
        updated();
    }
    @Override public int onStartCommand(Intent intent, int flags, int startId) { if (intent != null && STOP.equals(intent.getAction())) stopSelf(); return START_NOT_STICKY; }
    private synchronized void attach(BluetoothSocket socket) throws Exception {
        String address = socket.getRemoteDevice().getAddress(); if (links.containsKey(address) || links.size() >= 2) { socket.close(); return; }
        adapter.cancelDiscovery(); scanning = false;
        Link link = new Link(socket); links.put(address, link);
        try { io.execute(link::read); } catch (java.util.concurrent.RejectedExecutionException busy) { link.close(); throw busy; }
        updated();
    }
    private void broadcast(JSONObject envelope, Link except) {
        for (Link link : links.values()) if (link != except && link.authenticated) try { link.send(new JSONObject().put("type", "envelope").put("envelope", envelope)); } catch (Exception ignored) { }
    }
    private void updated() { MainActivity.nearbyCall("updated", new JSONObject()); }
    private static JSONObject call(String operation, JSONObject args) throws Exception { return MainActivity.nearbyCall(operation, args).get(20, TimeUnit.SECONDS); }
    private final class Link {
        final BluetoothSocket socket;
        final ExecutorService writer = new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, new ArrayBlockingQueue<>(4));
        final String challenge;
        volatile JSONObject contact;
        volatile boolean authenticated, closed;
        String remoteChallenge, ownId;
        long minute; int messages;
        Link(BluetoothSocket socket) { this.socket = socket; byte[] bytes = new byte[16]; new SecureRandom().nextBytes(bytes); StringBuilder text = new StringBuilder(); for (byte b : bytes) text.append(String.format(java.util.Locale.ROOT, "%02x", b & 255)); challenge = text.toString(); }
        void send(JSONObject frame) {
            if (closed) return;
            final boolean encrypted = authenticated;
            final String encoded = frame.toString();
            try { writer.execute(() -> { try {
                byte[] bytes;
                if (encrypted) {
                    JSONObject result = call("encrypt", new JSONObject().put("contact", contact).put("context", context()).put("frame", new JSONObject(encoded)));
                    byte[] sealed = android.util.Base64.decode(result.getString("packet"), android.util.Base64.URL_SAFE | android.util.Base64.NO_WRAP | android.util.Base64.NO_PADDING);
                    bytes = new byte[sealed.length + 1]; bytes[0] = 1; System.arraycopy(sealed, 0, bytes, 1, sealed.length);
                } else bytes = encoded.getBytes(StandardCharsets.UTF_8);
                NearbyWire.write(socket.getOutputStream(), bytes);
            } catch (Exception error) { close(); } }); } catch (java.util.concurrent.RejectedExecutionException busy) { }
        }
        void inventory() { ioInventory(); }
        private void ioInventory() {
            MainActivity.nearbyCall("inventory", new JSONObject()).thenAccept(result -> { try { send(new JSONObject().put("type", "inventory").put("ids", result.getJSONArray("ids"))); } catch (Exception ignored) { } });
        }
        String path(boolean outgoing) throws Exception {
            return "/nearby/v1/" + (outgoing ? challenge + "/" + remoteChallenge + "/" + ownId + "/" + contact.getString("id") : remoteChallenge + "/" + challenge + "/" + contact.getString("id") + "/" + ownId);
        }
        String context() throws Exception { return ownId.compareTo(contact.getString("id")) < 0 ? path(true) : path(false); }
        void read() {
            java.util.concurrent.ScheduledFuture<?> handshake = timer.schedule(this::close, 45, TimeUnit.SECONDS);
            try {
                JSONObject hello = call("hello", new JSONObject()); ownId = hello.getJSONObject("contact").getString("id");
                send(new JSONObject().put("type", "hello").put("version", 1).put("invite", hello.getString("invite")).put("challenge", challenge));
                while (!closed && !stopped) {
                    byte[] raw = NearbyWire.read(socket.getInputStream()); JSONObject frame;
                    if (raw[0] == 1) {
                        if (!authenticated) throw new IOException("Authenticate the nearby contact first");
                        String packet = android.util.Base64.encodeToString(java.util.Arrays.copyOfRange(raw, 1, raw.length), android.util.Base64.URL_SAFE | android.util.Base64.NO_WRAP | android.util.Base64.NO_PADDING);
                        frame = call("decrypt", new JSONObject().put("contact", contact).put("context", context()).put("packet", packet)).getJSONObject("frame");
                    } else {
                        if (authenticated) throw new IOException("Nearby session requires authenticated frames");
                        frame = new JSONObject(new String(raw, StandardCharsets.UTF_8));
                    }
                    String type = frame.getString("type");
                    if (type.equals("hello")) {
                        if (contact != null || frame.getInt("version") != 1) throw new IOException("Unsupported nearby handshake");
                        remoteChallenge = frame.getString("challenge"); if (!remoteChallenge.matches("[0-9a-f]{32}")) throw new IOException("Invalid nearby challenge");
                        contact = call("contact", new JSONObject().put("uri", frame.getString("invite"))).getJSONObject("contact"); if (contact.getString("id").equals(ownId)) throw new IOException("This is your own identity");
                        JSONObject proof = call("sign", new JSONObject().put("path", path(true)));
                        send(new JSONObject().put("type", "auth").put("time_ms", Long.parseLong(proof.getString("time_ms"))).put("signature", proof.getString("signature"))); continue;
                    }
                    if (type.equals("auth")) {
                        if (contact == null || authenticated) throw new IOException("Invalid nearby authentication sequence");
                        call("verify", new JSONObject().put("id", contact.getString("id")).put("path", path(false)).put("time_ms", frame.getLong("time_ms")).put("signature", frame.getString("signature")));
                        authenticated = true; handshake.cancel(false); problem = ""; call("connected", new JSONObject().put("contact", contact)); updated(); inventory(); continue;
                    }
                    if (!authenticated) throw new IOException("Authenticate the nearby contact first");
                    if (type.equals("inventory")) {
                        JSONObject missing = call("missing", new JSONObject().put("ids", frame.getJSONArray("ids"))); if (missing.getJSONArray("ids").length() > 0) send(new JSONObject().put("type", "want").put("ids", missing.getJSONArray("ids")));
                    } else if (type.equals("want")) {
                        JSONArray packets = call("packets", new JSONObject().put("ids", frame.getJSONArray("ids"))).getJSONArray("envelopes");
                        for (int i = 0; i < packets.length(); i++) send(new JSONObject().put("type", "envelope").put("envelope", packets.getJSONObject(i)));
                    } else if (type.equals("envelope")) {
                        long current = System.currentTimeMillis() / 60000; if (current != minute) { minute = current; messages = 0; } if (++messages > 240) throw new IOException("Nearby delivery rate exceeded");
                        JSONObject envelope = frame.getJSONObject("envelope"); JSONObject result = call("accept", new JSONObject().put("envelope", envelope)); send(new JSONObject().put("type", "ack").put("id", result.getString("id"))); if (result.getBoolean("new")) broadcast(envelope, this);
                    } else if (type.equals("ack")) {
                        String id = frame.getString("id"); if (!id.matches("[0-9a-f]{64}")) throw new IOException("Invalid nearby acknowledgment"); call("ack", new JSONObject().put("id", id));
                    } else throw new IOException("Unknown nearby frame");
                }
            } catch (Exception interrupted) { }
            finally { handshake.cancel(false); close(); }
        }
        void close() { if (closed) return; closed = true; try { socket.close(); } catch (IOException ignored) { } writer.shutdownNow(); links.remove(socket.getRemoteDevice().getAddress(), this); updated(); }
    }
    @Override public void onDestroy() {
        stopped = true; if (running == this) running = null;
        try { unregisterReceiver(discovery); } catch (Exception ignored) { }
        try { if (adapter != null) adapter.cancelDiscovery(); } catch (Exception ignored) { }
        try { if (server != null) server.close(); } catch (IOException ignored) { }
        for (Link link : links.values()) link.close(); timer.shutdownNow(); io.shutdownNow(); stopForeground(STOP_FOREGROUND_REMOVE); updated(); super.onDestroy();
    }
    @Override public IBinder onBind(Intent intent) { return null; }
}
