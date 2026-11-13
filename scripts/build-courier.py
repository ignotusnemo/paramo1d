#!/usr/bin/env python3
"""Build the Paramo1d Android application with its pinned verification parameters."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--ndk", required=True, type=Path)
parser.add_argument("--sdk", required=True, type=Path)
parser.add_argument("--java-home", required=True, type=Path)
parser.add_argument("--gradle", required=True, type=Path)
parser.add_argument("--artifacts", required=True, type=Path)
parser.add_argument("--go", required=True, type=Path)
parser.add_argument("--variant", choices=("debug", "release"), default="debug")
args = parser.parse_args()
if args.variant == "release":
    required = ("PARAMO1D_ANDROID_KEYSTORE_PATH", "PARAMO1D_ANDROID_STORE_PASSWORD", "PARAMO1D_ANDROID_KEY_ALIAS")
    missing = [name for name in required if not os.environ.get(name)]
    if missing:
        parser.error("release signing requires " + ", ".join(missing))
root = Path(__file__).resolve().parents[1]
profile = json.loads((root / "profiles/mainnet.json").read_text())
destination = root / "android/app/src/main/assets/parameters"
destination.mkdir(parents=True, exist_ok=True)
names = set()
names.add("release.id")
for category in ("artifacts", "matrix_caches"):
    for name, pin in profile[category].items():
        filename = name if category == "artifacts" else name + ".spancache"
        path = args.artifacts / filename
        encoded = path.read_bytes()
        if len(encoded) != pin["bytes"] or hashlib.sha256(encoded).hexdigest() != pin["sha256"]:
            parser.error("verification parameter does not match its release pin: " + filename)
        names.add(filename)
for name in profile["matrix_caches"]:
    filename = name + ".pmatrix"
    if not (args.artifacts / filename).is_file():
        parser.error("missing prepared matrix: " + filename)
    names.add(filename)
for existing in destination.iterdir():
    if existing.name not in names:
        parser.error("unexpected generated parameter file: " + existing.name)
for name in sorted(names - {"release.id"}):
    shutil.copy2(args.artifacts / name, destination / name)
release = "\n".join(name + ":" + hashlib.sha256((destination / name).read_bytes()).hexdigest() for name in sorted(names - {"release.id"}))
(destination / "release.id").write_text(hashlib.sha256(release.encode()).hexdigest())
subprocess.run([sys.executable, str(root / "scripts/check-upstream.py")], check=True)
subprocess.run([sys.executable, str(root / "scripts/build-android.py"), "--ndk", str(args.ndk.resolve())], cwd=root, check=True)
jni = root / "android/app/src/main/jniLibs/arm64-v8a"
jni.mkdir(parents=True, exist_ok=True)
shutil.copy2(root / "target/aarch64-linux-android/release/libparamo1d.so", jni / "libparamo1d.so")
tunnel_env = os.environ.copy()
tunnel_env.update(CGO_ENABLED="1", GOOS="android", GOARCH="arm64")
tunnel_env["CC"] = str(args.ndk.resolve() / "toolchains/llvm/prebuilt/linux-x86_64/bin/aarch64-linux-android26-clang")
subprocess.run([str(args.go.resolve()), "-C", str(root / "tunnel"), "build", "-trimpath", "-ldflags=-s -w", "-buildmode=c-shared", "-o", str(jni / "libparamo1d_tunnel.so"), "./cmd/mobile"], env=tunnel_env, check=True)
env = os.environ.copy()
env.update(JAVA_HOME=str(args.java_home.resolve()), ANDROID_HOME=str(args.sdk.resolve()), ANDROID_SDK_ROOT=str(args.sdk.resolve()))
env["PATH"] = str(args.java_home.resolve() / "bin") + os.pathsep + env["PATH"]
task = ":app:assembleRelease" if args.variant == "release" else ":app:assembleDebug"
subprocess.run([str(args.gradle.resolve()), "-p", str(root / "android"), ":app:testDebugUnitTest", task, "--console=plain", "--no-daemon"], env=env, check=True)
apk = root / f"android/app/build/outputs/apk/{args.variant}/app-{args.variant}.apk"
print(json.dumps({"apk": str(apk), "bytes": apk.stat().st_size, "sha256": hashlib.sha256(apk.read_bytes()).hexdigest()}))
