"""Replay unmodified canonical certificate programs in a restored directory.
Usage: /usr/bin/python3.10 -B replay.py /work/fresh-candidate /work/fresh-evidence
Before replay: /usr/bin/python3.10 /task/RESTORE_CANDIDATE.py --out /work/fresh-candidate
Run with assertions enabled. bridge.py writes /work/bridge and /work/bridge.logs.
"""
from pathlib import Path
import subprocess, sys, os, concurrent.futures, time, json, hashlib
assert __debug__
candidate=Path(sys.argv[1]).resolve()
dest=Path(sys.argv[2]).resolve()
dest.mkdir(parents=True,exist_ok=True)
jobs=['verify.py --endpoint','bridge.py','general.py','early.py','weighted.py','smallprod.py',
      'mverify.py','tradeoff.py','receipts.py','spectral_repair.py','power_bridge.py','gap_repair.py']
def run(s):
    a=[sys.executable,'-B','-u',*s.split()]; n=s.split('.')[0]
    t=time.monotonic()
    with (dest/(n+'.replay')).open('w') as f,(dest/(n+'.stderr')).open('w') as e:
        r=subprocess.run(a,stdout=f,stderr=e,cwd=candidate,env={**os.environ,'LC_ALL':'C'})
    print(n,r.returncode,time.monotonic()-t,flush=True)
    return [a,r.returncode]
with concurrent.futures.ThreadPoolExecutor(4) as e:
    (dest/'replay_status.json').write_text(json.dumps(list(e.map(run,jobs)),indent=2))
