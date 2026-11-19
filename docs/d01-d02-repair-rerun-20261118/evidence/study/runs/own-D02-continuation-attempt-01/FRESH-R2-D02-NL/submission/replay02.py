from pathlib import Path
import sys, hashlib, json, subprocess
p=Path(__file__).resolve().parent
t=Path('/task')
ix=json.loads((t/'SOURCE_INDEX.json').read_text())
root=Path(json.loads((t/'RUNTIME_PATHS.json').read_text())['paper_root'])
assert root==Path(ix['root'])
def digest(b):return hashlib.sha256(b).hexdigest()
assert (p/'INPUT_CONTRACT.json').read_bytes()==(t/'INPUT_CONTRACT.json').read_bytes()
for s in ix['sources']:
    for k in ('pdf','text'):
        f=root/s[k]; b=f.read_bytes(); h=digest(b)
        assert h==s[k+'_sha256'], f.name
        print('source',f.name,len(b),h,flush=True)
py='/usr/bin/python3.10'
def run(args,out):
    b=subprocess.check_output(args,cwd=p)
    assert b==(p/out).read_bytes(), out
    print('verified',out,digest(b),flush=True)
for branch,n in [('7/8','b0'),('27/32','d2')]:
    run([py,'-B','search02.py',branch],f'order_{n}.txt')
    run([py,'-B','windows02.py',branch],f'window_{n}.txt')
run([py,'-B','m02check.py'],'m02_result.txt')
run([py,'-B','global02.py'],'global02_result.txt')
if '--finite' in sys.argv:
    exe='/work/finite02_replay'
    subprocess.run(['/usr/bin/g++','-O3','-std=c++17','finite02.cpp','-o',exe],cwd=p,check=True)
    run([exe],'finite02_result.txt')
