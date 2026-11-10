#!/usr/bin/env python3
"""Build the ARM64 Android verification library with an installed NDK."""
import argparse
import os
import shlex
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--ndk", required=True, type=Path)
parser.add_argument("--isolated-testnet", action="store_true")
parser.add_argument("--cli", action="store_true", help="also build the Android command-line verifier")
args = parser.parse_args()
toolchain = args.ndk.resolve() / "toolchains/llvm/prebuilt/linux-x86_64"
compiler = toolchain / "bin/aarch64-linux-android26-clang"
if not compiler.is_file():
    parser.error("an Android NDK for Linux with the ARM64 API 26 compiler is required")

env = os.environ.copy()
env.update({
    "CARGO_TARGET_AARCH64_LINUX_ANDROID_LINKER": str(compiler),
    "CC_aarch64_linux_android": str(compiler),
    "AR_aarch64_linux_android": str(toolchain / "bin/llvm-ar"),
    "BINDGEN_EXTRA_CLANG_ARGS_aarch64_linux_android":
        "--sysroot=" + str(toolchain / "sysroot") + " --target=aarch64-linux-android26",
})
# Android verification requires NEON and PMULL. Compile their arithmetic
# directly so field operations can inline across the protocol kernels.
flags = env.get("CARGO_ENCODED_RUSTFLAGS")
flags = flags.split("\x1f") if flags is not None else shlex.split(env.get("RUSTFLAGS", ""))
flags += ["-C", "target-feature=+neon,+aes"]
env["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join(flags)
env.pop("RUSTFLAGS", None)
command = ["cargo", "build", "--locked", "--release", "--target", "aarch64-linux-android", "--lib"]
if args.cli:
    command += ["--bin", "paramo1d"]
if args.isolated_testnet:
    command += ["--features", "isolated-testnet"]
raise SystemExit(subprocess.call(command, env=env, cwd=Path(__file__).resolve().parents[1]))
