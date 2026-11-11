package org.parano1d.courier;

import android.graphics.Color;
import android.os.Bundle;
import android.view.Gravity;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;
import com.journeyapps.barcodescanner.CaptureActivity;
import com.journeyapps.barcodescanner.DecoratedBarcodeView;

public final class QrScanActivity extends CaptureActivity {
    private DecoratedBarcodeView scanner;
    private boolean torch;

    @Override protected DecoratedBarcodeView initializeContent() {
        scanner = super.initializeContent();
        return scanner;
    }

    @Override protected void onCreate(Bundle state) {
        super.onCreate(state);
        if (!getSharedPreferences("interface", MODE_PRIVATE).getBoolean("allow_screenshots", false)) getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_SECURE);
        getWindow().setStatusBarColor(Color.rgb(16, 20, 19));
        getWindow().setNavigationBarColor(Color.rgb(16, 20, 19));
        boolean contact = "contact".equals(getIntent().getStringExtra("paramo1d.scan.kind"));
        float density = getResources().getDisplayMetrics().density;
        int padding = Math.round(12 * density);
        LinearLayout toolbar = new LinearLayout(this);
        toolbar.setGravity(Gravity.CENTER_VERTICAL); toolbar.setPadding(padding, padding, padding, padding);
        toolbar.setBackgroundColor(0xe6101413);
        Button back = new Button(this); back.setText("‹"); back.setTextSize(28); back.setTextColor(Color.WHITE);
        back.setBackgroundColor(Color.TRANSPARENT); back.setContentDescription("Cancel scan"); back.setOnClickListener(view -> finish());
        toolbar.addView(back, new LinearLayout.LayoutParams(Math.round(48 * density), Math.round(48 * density)));
        TextView title = new TextView(this); title.setText(contact ? "Scan a contact" : "Scan NOID address"); title.setTextColor(Color.WHITE); title.setTextSize(18);
        toolbar.addView(title, new LinearLayout.LayoutParams(0, -2, 1));
        if (getPackageManager().hasSystemFeature(android.content.pm.PackageManager.FEATURE_CAMERA_FLASH)) {
            Button flash = new Button(this); flash.setText("Flash"); flash.setAllCaps(false); flash.setTextColor(Color.WHITE); flash.setBackgroundColor(Color.TRANSPARENT);
            flash.setOnClickListener(view -> { torch = !torch; if (torch) scanner.setTorchOn(); else scanner.setTorchOff(); flash.setText(torch ? "Flash on" : "Flash"); });
            toolbar.addView(flash);
        }
        FrameLayout content = findViewById(android.R.id.content);
        content.addView(toolbar, new FrameLayout.LayoutParams(-1, -2, Gravity.TOP));
        if (android.os.Build.VERSION.SDK_INT >= 35) toolbar.setOnApplyWindowInsetsListener((view, insets) -> {
            android.graphics.Insets bars = insets.getInsets(android.view.WindowInsets.Type.systemBars() | android.view.WindowInsets.Type.displayCutout());
            view.setPadding(padding + bars.left, padding + bars.top, padding + bars.right, padding); return insets;
        });
    }
}
