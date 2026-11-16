"""Check the actual pinned Lean runtime; bin/lean alone is a thin launcher."""
from pathlib import Path
import hashlib,json,subprocess

ROOT=Path(__file__).resolve().parents[1]

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(4*1024**2),b''):h.update(b)
    return h.hexdigest()

def check_runtime(toolchain):
    pins=json.loads((ROOT/'COMPILER_RUNTIME.lock.json').read_text())
    toolchain=Path(toolchain)
    for rel,row in pins['files'].items():
        p=toolchain/rel
        if not p.is_file() or p.stat().st_size!=row['bytes'] or sha(p)!=row['sha256']:
            raise ValueError('pinned runtime mismatch: '+rel)
    version=subprocess.check_output([str(toolchain/'bin/lean'),'--version'],text=True).strip()
    if version!=pins['compiler_version']:raise ValueError('actual Lean version/commit mismatch')
    return dict(version=version,runtime_lock_sha256=sha(ROOT/'COMPILER_RUNTIME.lock.json'),files=pins['files'])
