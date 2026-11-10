#!/usr/bin/env python3
"""Fetch and check the pinned public Android verification parameters."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import urllib.request

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", required=True, type=Path)
parser.add_argument("--archive", type=Path, help="use an existing archive with the pinned hash")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
pin = json.loads((root / "android/build-inputs.json").read_text())["parameters"]
profile = json.loads((root / "profiles/mainnet.json").read_text())
names = set(profile["artifacts"])
names.update(name + ".spancache" for name in profile["matrix_caches"])
names.update(name + ".pmatrix" for name in profile["matrix_caches"])
with tempfile.TemporaryDirectory(prefix="paramo1d-parameters-") as temporary:
    archive = args.archive or Path(temporary) / "parameters.tar.gz"
    if args.archive is None:
        request = urllib.request.Request(pin["url"], headers={"User-Agent": "Paramo1d-build"})
        with urllib.request.urlopen(request, timeout=60) as response, archive.open("wb") as output:
            copied = 0
            while data := response.read(1024 * 1024):
                copied += len(data)
                if copied > pin["bytes"]:
                    raise ValueError("parameter archive exceeds its pinned size")
                output.write(data)
    if archive.stat().st_size != pin["bytes"]:
        raise ValueError("parameter archive size does not match its pin")
    with archive.open("rb") as source:
        digest = hashlib.file_digest(source, "sha256").hexdigest()
    if digest != pin["sha256"]:
        raise ValueError("parameter archive hash does not match its pin")
    args.output.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r:gz") as container:
        members = container.getmembers()
        if len(members) != len(names) or {member.name for member in members} != names:
            raise ValueError("unexpected verification parameter inventory")
        for member in members:
            if not member.isfile() or not 0 < member.size <= 64 * 1024 * 1024:
                raise ValueError("unexpected verification parameter entry")
            destination = args.output / member.name
            if destination.is_symlink():
                raise ValueError("verification parameter destination is a symlink")
            with container.extractfile(member) as source, destination.open("wb") as output:
                shutil.copyfileobj(source, output)
print(json.dumps({"parameters": str(args.output), "archive_sha256": pin["sha256"], "files": len(names)}))
