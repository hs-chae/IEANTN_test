"""Replay published final checks using only local tools and the bound packet."""
import hashlib, json, os, subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
os.chdir(HERE)
PY=['/usr/bin/python3.10','-B']
idx=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
bound=json.loads(Path('/task/RUNTIME_PATHS.json').read_text())["paper_root"]
assert idx['root']==bound
expected=json.loads(Path('source_receipt.json').read_text())
seen={}
for row in idx['sources']:
    for k in ('pdf','text'):
        n=row[k]
        h=hashlib.sha256((Path(bound)/n).read_bytes()).hexdigest()
        assert h==row[k+'_sha256']==expected[n]
        seen[n]=h
assert seen==expected

def verify(cmd, result):
    data=subprocess.check_output(cmd)
    assert data==Path(result).read_bytes(),result
    print('verified',result,hashlib.sha256(data).hexdigest(),flush=True)
verify(PY+['certify.py'],'gap_envelope.txt')
verify(PY+['edge.py'],'edge_result.txt')
verify(PY+['mertens_cert.py'],'mertens_result.txt')
exe='/work/d01_finite_replay'
subprocess.run(['/usr/bin/g++','-Wall','-Wextra','-O3','-std=c++17','finite.cpp','-o',exe],check=True)
verify([exe],'finite_final.txt')
verify(PY+['cutoffs.py'],'cutoffs_result.txt')

