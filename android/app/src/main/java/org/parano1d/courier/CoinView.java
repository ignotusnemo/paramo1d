package org.parano1d.courier;

import android.animation.ValueAnimator;
import android.content.Context;
import android.graphics.Camera;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.LinearGradient;
import android.graphics.Matrix;
import android.graphics.Paint;
import android.graphics.Shader;
import android.graphics.drawable.Drawable;
import android.view.View;
import android.view.animation.LinearInterpolator;

/** The Parano1d mark on a turning coin, drawn locally at the view's resolution. */
public final class CoinView extends View {
    private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Camera camera = new Camera();
    private final Matrix projection = new Matrix();
    private final Drawable face;
    private final ValueAnimator turn;
    private Bitmap image;
    private Shader edge, reflection;
    private float radius, degrees;
    private boolean played;
    private long nextFrame;

    public CoinView(Context context) {
        super(context);
        face = context.getDrawable(R.drawable.parano1d_mark).mutate();
        paint.setFilterBitmap(true);
        setContentDescription("Parano1d");
        setImportantForAccessibility(IMPORTANT_FOR_ACCESSIBILITY_YES);
        camera.setLocation(0, 0, -8 * getResources().getDisplayMetrics().density);
        turn = ValueAnimator.ofFloat(0, 360);
        turn.setDuration(1800);
        turn.setRepeatCount(0);
        turn.setInterpolator(new LinearInterpolator());
        turn.addUpdateListener(animation -> {
            degrees = (float) animation.getAnimatedValue();
            long now = android.os.SystemClock.uptimeMillis();
            if (now >= nextFrame || degrees >= 360) { nextFrame = now + 33; invalidate(); }
        });
    }

    @Override protected void onSizeChanged(int width, int height, int oldWidth, int oldHeight) {
        radius = Math.min(width, height) * .37f;
        int bound = Math.round(radius);
        if (bound <= 0) return;
        image = Bitmap.createBitmap(bound * 2, bound * 2, Bitmap.Config.ARGB_8888);
        face.setBounds(0, 0, image.getWidth(), image.getHeight());
        face.draw(new Canvas(image));
        edge = new LinearGradient(0, -radius, 0, radius,
            new int[]{0xff234f41, 0xff64f4ae, 0xff123f31, 0xff39be7f, 0xff143d31},
            new float[]{0, .2f, .5f, .77f, 1}, Shader.TileMode.CLAMP);
        reflection = new LinearGradient(-radius, -radius, radius, radius,
            new int[]{0x00ffffff, 0x38ffffff, 0x00ffffff},
            new float[]{0, .36f, .72f}, Shader.TileMode.CLAMP);
    }

    @Override protected void onDraw(Canvas canvas) {
        super.onDraw(canvas);
        if (radius <= 0 || image == null) return;
        double radians = Math.toRadians(degrees);
        float cosine = Math.abs((float) Math.cos(radians));
        float sine = (float) Math.sin(radians);
        float depth = Math.abs(sine) * radius * .12f;
        float halfWidth = radius * cosine;
        int base = canvas.save();
        canvas.translate(getWidth() / 2f, getHeight() / 2f - radius * .12f);

        paint.setShader(null); paint.setStyle(Paint.Style.FILL);
        paint.setColor(Color.argb(26, 7, 18, 13));
        float shadowWidth = radius * (.28f + .65f * cosine);
        canvas.drawOval(-shadowWidth, radius * 1.22f, shadowWidth, radius * 1.34f, paint);

        paint.setShader(edge); paint.setAlpha(255);
        canvas.drawOval(-halfWidth - depth, -radius, halfWidth + depth, radius, paint);
        paint.setShader(null); paint.setColor(0x8058d99c); paint.setStrokeWidth(Math.max(1, radius / 90));
        for (int step = -5; depth > 1 && step <= 5; step++) {
            float y = radius * step / 6f;
            float span = (float) Math.sqrt(1 - y * y / (radius * radius));
            canvas.drawLine((-halfWidth - depth) * span, y, (halfWidth + depth) * span, y, paint);
        }

        if (cosine > .025f) {
            int side = canvas.save();
            canvas.translate(sine * radius * .06f, 0);
            float faceAngle = (degrees + 90) % 180 - 90;
            camera.save(); camera.rotateY(faceAngle); camera.getMatrix(projection); camera.restore();
            canvas.concat(projection);
            paint.setColor(Color.WHITE);
            canvas.drawBitmap(image, -image.getWidth() / 2f, -image.getHeight() / 2f, paint);
            paint.setShader(reflection); paint.setAlpha(70 + Math.round(110 * Math.abs(sine)));
            canvas.drawCircle(0, 0, radius * .97f, paint);
            paint.setShader(null); paint.setAlpha(255);
            canvas.restoreToCount(side);
        }
        canvas.restoreToCount(base);
    }

    private void updateAnimation() {
        if (turn == null) return;
        boolean motion = ValueAnimator.areAnimatorsEnabled();
        if (!isAttachedToWindow() || !isShown() || getWindowVisibility() != VISIBLE || !motion) {
            if (turn.isStarted()) turn.cancel();
            played = false; nextFrame = 0;
            if (degrees != 0) { degrees = 0; invalidate(); }
            return;
        }
        if (hasWindowFocus()) {
            if (turn.isPaused()) turn.resume();
            else if (!played) { played = true; nextFrame = 0; turn.start(); }
        } else if (turn.isStarted() && !turn.isPaused()) turn.pause();
    }

    @Override protected void onAttachedToWindow() { super.onAttachedToWindow(); updateAnimation(); }
    @Override protected void onDetachedFromWindow() { turn.cancel(); super.onDetachedFromWindow(); }
    @Override protected void onVisibilityChanged(View changedView, int visibility) { super.onVisibilityChanged(changedView, visibility); updateAnimation(); }
    @Override protected void onWindowVisibilityChanged(int visibility) { super.onWindowVisibilityChanged(visibility); updateAnimation(); }
    @Override public void onWindowFocusChanged(boolean hasFocus) { super.onWindowFocusChanged(hasFocus); updateAnimation(); }
}
