#!/usr/bin/env python3
"""Check migrated input hashes and byte-preserving module-interface changes."""
from pathlib import Path
import hashlib, io, json, re, subprocess, tarfile

def skip_comments(text,pos):
 while pos<len(text):
  if text[pos].isspace():pos+=1
  elif text.startswith('--',pos):
   n=text.find('\n',pos);pos=len(text) if n<0 else n+1
  elif text.startswith('/-',pos):
   pos+=2;depth=1
   while pos<len(text) and depth:
    if text.startswith('/-',pos):depth+=1;pos+=2
    elif text.startswith('-/',pos):depth-=1;pos+=2
    else:pos+=1
  else:break
 return pos

def port(data):
 text=data.decode('utf8');i=skip_comments(text,0)
 if re.match(r'module\b',text[i:]):return data
 imports=[]
 while re.match(r'(?:public )?import\s',text[i:]):
  end=text.find('\n',i)
  if end<0:end=len(text)
  imports.append((i,end));i=skip_comments(text,end)
 if not imports:raise ValueError('No leading import header')
 last=imports[-1][1]
 edits=[(last,last,'\n\n@[expose] public section')]
 for start,end in imports:
  if text.startswith('import ',start):edits.append((start,start,'public '))
 for start,end,value in sorted(edits,reverse=True):text=text[:start]+value+text[end:]
 return ('module\n\n'+text).encode()

root = Path(__file__).resolve().parents[1]
ledger = json.loads((root / "docs/palomar/MIGRATION_LEDGER.json").read_text())
archive = subprocess.check_output(["git", "archive", ledger["baseline_commit"]], cwd=root)
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    original = {m.name: tar.extractfile(m).read() for m in tar if m.isfile()}
manifest = json.loads((root / ledger["baseline_manifest"]).read_text())
changes = {c["path"]: c for c in ledger["changes"]}
for row in manifest["files"]:
    path = row["path"]
    current = (root / path).read_bytes()
    baseline = original[path]
    assert hashlib.sha256(baseline).hexdigest() == row["sha256"], path
    if path in changes:
        change = changes[path]
        assert hashlib.sha256(baseline).hexdigest() == change["before_sha256"], path
        assert hashlib.sha256(current).hexdigest() == change["after_sha256"], path
        if change["kind"] == "module-interface-only":
            assert current == port(baseline), path
    else:
        assert current == baseline, path
for path, change in changes.items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == change["after_sha256"], path
    if change["kind"] == "module-interface-only":
        assert (root / path).read_bytes() == port(original[path]), path
assert (root / "LICENSE").read_bytes() == subprocess.check_output(["git", "show", "HEAD:LICENSE"], cwd=root)
for row in ledger.get("additional_statement_inputs", []):
    assert hashlib.sha256((root / row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
print("Verified", len(manifest["files"]), "baseline inputs against", len(changes), "explicitly recorded migration changes; interface-only files retain original declaration/proof text.")
