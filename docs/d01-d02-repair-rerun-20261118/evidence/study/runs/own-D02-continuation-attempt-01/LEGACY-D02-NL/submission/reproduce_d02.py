"""Replay the current D02 assertions; optional 'inheritance' runs old replay too."""
from pathlib import Path
import hashlib, json, os, subprocess, tempfile, sys

p=Path(__file__).resolve().parent
py='/usr/bin/python3.10'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
def sha(buf): return hashlib.sha256(buf).hexdigest()
if __name__=='__main__':
    lock=json.loads((p/'LOCK.json').read_text())
    assert set(lock)=={'files'}
    names=[e['path'] for e in lock['files']]
    assert len(set(names))==len(names)
    assert set(names)=={f.name for f in p.iterdir() if f.is_file() and f.name!='LOCK.json'}
    for e in lock['files']:
        assert set(e)=={'path','sha256'} and Path(e['path']).name==e['path']
        assert sha((p/e['path']).read_bytes())==e['sha256']
    root=Path(tempfile.mkdtemp(prefix='d02-certificate-',dir='/work'))
    specs=[
      ('gap_d02.py','base',13,'certified'),('gap_d02.py','new',15,'certified'),
      ('gap_d02.py','high',26,'certified'),('extra_gap.py','far',20,'certified far'),
      ('extra_gap.py','try',5,'certified'),('mertens_d02.py','analytic',18,'ray'),
      ('mertens_d02.py','log',9,'closed ray'),
      ('mertens_d02.py','weighted-root',2,'weighted exact root bracket'),
      ('mertens_d02.py','three-roots',3,'exact root bracket'),
    ]
    for cmd,opt,n,keyword in specs:
        out=subprocess.check_output([py,cmd,opt],cwd=p,env=env)
        lines=out.decode().splitlines()
        assert sum(keyword in line and 'not certified' not in line for line in lines)==n,(cmd,opt)
        if opt not in ('try','far'):
            assert 'rejected' not in out.decode() and 'not certified' not in out.decode()
        (root/(cmd+'-'+opt+'.out')).write_bytes(out)
        print(cmd,opt,sha(out),flush=True)
    for args in [['119','.25665','unweighted'],['285','.25665'],['200','.30']]:
        out=subprocess.check_output([py,'mertens_d02.py','finite']+args,cwd=p,env=env)
        assert out.startswith(b'finite closed log-gap cells')
        (root/('finite-'+args[0]+'.out')).write_bytes(out)
        print('finite',args,sha(out),flush=True)
    out=subprocess.check_output([py,'compare_d02.py'],cwd=p,env=env)
    (root/'compare.out').write_bytes(out)
    print('compare',sha(out),flush=True)
    if sys.argv[1:]==['inheritance']:
        subprocess.run([py,'D01_repaired_replay.py'],cwd=p,env=env,check=True)
    print('D02 replay finished:',root,flush=True)

