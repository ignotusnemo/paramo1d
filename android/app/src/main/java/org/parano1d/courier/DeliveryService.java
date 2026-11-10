package org.parano1d.courier;

import android.app.*;
import android.content.Intent;
import android.os.IBinder;
import android.content.pm.ServiceInfo;
import org.json.JSONObject;
import java.util.concurrent.*;

/** Background message delivery, independent of the foreground wallet node. */
public final class DeliveryService extends Service {
    private static volatile boolean running;
    private final ScheduledExecutorService timer = Executors.newSingleThreadScheduledExecutor();
    static boolean isRunning() { return running; }
    @Override public void onCreate() {
        super.onCreate(); running = true; MainActivity.initializeDelivery(getApplicationContext());
        NotificationManager manager = getSystemService(NotificationManager.class);
        manager.createNotificationChannel(new NotificationChannel("delivery", "Message delivery", NotificationManager.IMPORTANCE_LOW));
        PendingIntent open = PendingIntent.getActivity(this, 0, new Intent(this, MainActivity.class), PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        PendingIntent stop = PendingIntent.getService(this, 0, new Intent(this, DeliveryService.class).setAction("stop"), PendingIntent.FLAG_IMMUTABLE | PendingIntent.FLAG_UPDATE_CURRENT);
        Notification notification = new Notification.Builder(this, "delivery").setSmallIcon(R.drawable.ic_nearby).setContentTitle("Paramo1d delivery is on").setContentText("Messages retry when a connection is available.").setContentIntent(open).setOngoing(true).addAction(new Notification.Action.Builder(null, "Stop delivery", stop).build()).build();
        if (android.os.Build.VERSION.SDK_INT >= 34) startForeground(72, notification, ServiceInfo.FOREGROUND_SERVICE_TYPE_REMOTE_MESSAGING); else startForeground(72, notification);
        timer.scheduleWithFixedDelay(() -> MainActivity.deliveryPoll(), 1, 15, TimeUnit.SECONDS);
    }
    @Override public int onStartCommand(Intent intent, int flags, int startId) {
        if (intent != null && "stop".equals(intent.getAction())) { MainActivity.stopDelivery(); stopSelf(); }
        return START_STICKY;
    }
    @Override public void onDestroy() { running = false; timer.shutdownNow(); stopForeground(STOP_FOREGROUND_REMOVE); super.onDestroy(); }
    @Override public IBinder onBind(Intent intent) { return null; }
}
