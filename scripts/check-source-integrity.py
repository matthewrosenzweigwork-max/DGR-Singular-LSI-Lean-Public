#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text())
for row in manifest["files"]:
    path = root / row["path"]
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
        raise SystemExit("Source identity mismatch: " + row["path"])
print("Verified", len(manifest["files"]), "source/configuration files.")
