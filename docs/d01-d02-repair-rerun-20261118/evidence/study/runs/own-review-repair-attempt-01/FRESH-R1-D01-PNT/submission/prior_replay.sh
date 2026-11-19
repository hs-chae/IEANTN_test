#!/bin/bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd /work/submission
/usr/bin/python3.10 -c 'from pathlib import Path; Path("/work/replay").mkdir(exist_ok=True)'
/usr/bin/g++ -std=c++17 -O3 small_end.cpp -o /work/small_end
/usr/bin/g++ -std=c++17 -O3 finite.cpp -o /work/replay/finite
/usr/bin/g++ -std=c++17 -O2 -fsanitize=undefined -fno-sanitize-recover=undefined finite.cpp -o /work/replay/finite_ubsan
/usr/bin/g++ -std=c++17 -O3 finite_trials.cpp -o /work/replay/finite_trials
/usr/bin/python3.10 check.py > /work/replay/gap_evidence.txt
/usr/bin/python3.10 check.py --basic > /work/replay/gap_basic_evidence.txt
/usr/bin/python3.10 mertens_check.py > /work/replay/mertens_evidence.txt
/usr/bin/python3.10 mertens_check.py --basic >> /work/replay/mertens_evidence.txt
/work/replay/finite > /work/replay/finite_evidence.txt
/work/replay/finite_ubsan > /work/replay/finite_ubsan_evidence.txt
/work/replay/finite_trials > /work/replay/finite_trials_evidence.txt
/usr/bin/python3.10 - <<'VERIFY'
from pathlib import Path
import hashlib, json
actual={p.name for p in Path('.').iterdir() if p.is_file() and p.name!='LOCK.json'}
manifest=json.loads(Path('LOCK.json').read_text())['files']
assert actual=={r['path'] for r in manifest} and len(manifest)==len(actual)
for r in manifest:
    p=Path(r['path'])
    assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],p
    if p.name.endswith('_evidence.txt'):
        assert p.read_bytes()==(Path('/work/replay')/p).read_bytes(),p
print('All manifest and regenerated-evidence comparisons passed')
VERIFY
