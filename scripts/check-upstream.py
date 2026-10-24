#!/usr/bin/env python3
"""Verify the frozen source inventory and explicit client adapters."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
vendor = root / "vendor/parano1d"
upstream = json.loads((root / "vendor/upstream.json").read_text())
overrides = json.loads((root / "vendor/client-overrides.json").read_text())["files"]
actual = {str(path.relative_to(vendor)) for path in vendor.rglob("*") if path.is_file()}
assert actual == set(upstream["files"]), "vendored source inventory changed"
for relative, original in upstream["files"].items():
    expected = overrides.get(relative, original)
    digest = hashlib.sha256((vendor / relative).read_bytes()).hexdigest()
    assert digest == expected, "source changed: " + relative
assert set(overrides) <= actual, "unknown client override"
print(json.dumps({"commit": upstream["commit"], "files": len(actual), "client_adapters": len(overrides)}))

mdbx = root / "vendor/mdbx-sys"
upstream = json.loads((root / "vendor/mdbx-sys.upstream.json").read_text())
overrides = json.loads((root / "vendor/mdbx-sys.overrides.json").read_text())["files"]
actual = {str(path.relative_to(mdbx)) for path in mdbx.rglob("*") if path.is_file()}
assert actual == set(upstream["files"]), "MDBX source inventory changed"
for relative, original in upstream["files"].items():
    expected = overrides.get(relative, original)
    assert hashlib.sha256((mdbx / relative).read_bytes()).hexdigest() == expected, "MDBX source changed: " + relative
print(json.dumps({"package": upstream["package"], "version": upstream["version"], "files": len(actual), "client_adapters": len(overrides)}))
