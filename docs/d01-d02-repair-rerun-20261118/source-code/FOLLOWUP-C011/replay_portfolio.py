"""Run the current proof certificates and emit receipts. Assert exit status."""
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,subprocess,time
from pathlib import Path

def run(stem):
    argv=['/usr/bin/python3.10',stem+'.py']
    t=time.monotonic()
    p=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    o=stem+('.json' if stem=='source_rows' else '.log')
    if not p.returncode:
        Path(o).write_bytes(p.stdout)
    return dict(argv=argv,source_sha256=hashlib.sha256(Path(argv[1]).read_bytes()).hexdigest(),
                exit=p.returncode,seconds=round(time.monotonic()-t,3),stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),
                stdout_file=o if not p.returncode else None,stderr=p.stderr.decode())

if __name__=='__main__':
    with ThreadPoolExecutor(max_workers=5) as pool:
        names=['certificate','refine','checks','endpoint','small','source_rows','upgrade']
        rows=[]
        for r in pool.map(run,names):
            rows.append(r)
            print(r['argv'][-1],r['exit'],r['seconds'],flush=True)
    Path('replay_repair.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert all(r['exit']==0 for r in rows)
