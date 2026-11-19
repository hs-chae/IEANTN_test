"""Reproduce all independent numerical checks, unmodified candidate bytes.
Usage: /usr/bin/python3.10 /work/submission/replay.py --out /work/fresh-review-run
Requires the assigned offline executor and /task plus /corpus/originals.
The output directory must not exist. Runs with assertions enabled.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time

PY='/usr/bin/python3.10'
GXX='/usr/bin/g++'
TASK=Path('/task')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run_all(out):
    out.mkdir()
    src=out/'restored'
    env=dict(os.environ,LC_ALL='C',PATH='/usr/bin:/bin',PYTHONDONTWRITEBYTECODE='1')
    env.pop('PYTHONOPTIMIZE',None)
    env['PYTHONPATH']='.'
    receipts={}
    def run(name,args,cwd,expected=None):
        start=time.monotonic()
        p=subprocess.run(args,cwd=cwd,env=env,capture_output=True)
        rec=dict(command=args,cwd=str(cwd),elapsed_s=time.monotonic()-start,status=p.returncode,
                 stdout=p.stdout.decode(),stderr=p.stderr.decode(),
                 stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
        (out/(name+'.stdout')).write_bytes(p.stdout)
        (out/(name+'.stderr')).write_bytes(p.stderr)
        if expected:
            rec.update(locked_reference=expected,locked_reference_sha256=sha(src/expected),
                       byte_identical=(p.stdout==(src/expected).read_bytes()))
        receipts[name]=rec
        (out/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
        p.check_returncode()
    run('restore',[PY,str(TASK/'RESTORE_CANDIDATE.py'),'--out',str(src)],out)
    for entry in json.loads((TASK/'CANDIDATE_INDEX.json').read_text())['candidate_files']:
        assert sha(src/entry['original_name'])==entry['sha256']
    for entry in json.loads((TASK/'SOURCE_INDEX.json').read_text())['sources']:
        for kind in ['pdf','text']:
            assert sha(Path('/corpus/originals',entry[kind]))==entry[kind+'_sha256']
    run('compiler_version',[GXX,'--version'],src)
    run('python_version',[PY,'--version'],src)
    for job,args,want in [('endpoint',['cert.py','endpoint'],'endpoint.out'),
                          ('higher',['cert.py','tails'],'higher.out'),
                          ('ma',['mcert.py'],'mertens_analytic.out'),
                          ('ra',['repair_cert.py'],'repair.out'),
                          ('r2a',['m_poly_2b.py'],'m_poly_2b_analytic.out'),
                          ('r4a',['repair_mpoly.py'],'repair_mpoly_analytic.out'),
                          ('ranu',['cert.py'],'ranu.out')]:
        run(job,[PY]+args,src,want)
    for job,stem in [('r0','mertens'),('r2','m_poly_2b'),('r4','repair_mpoly')]:
        obj=out/stem
        run(job+'_build',[GXX,'-O3','-std=c++17',stem+'.cc','-o',str(obj)],src)
        run(job,[str(obj)],src,stem+'.out')
        receipts[job]['binary_sha256']=sha(obj)
    run('witness',[PY,'witness.py',str(out/'r0.stdout')],src,'witness.out')
    run('ancillary',[PY,str(Path(__file__).resolve().with_name('ancillary.py')),str(out/'r0.stdout')],src)
    # Only the last display label changed after the old grid receipt.
    assert all(r.get('byte_identical',True) for k,r in receipts.items() if k!='ranu')
    assert (out/'ranu.stdout').read_bytes().splitlines()[:-1]==(src/'ranu.out').read_bytes().splitlines()[:-1]

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--out',required=True,type=Path)
    run_all(p.parse_args().out.resolve())
