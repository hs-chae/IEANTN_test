#!/usr/bin/python3.10
"""Reproduce exact candidate computations used in the review.
Run with /usr/bin/python3.10 replay_review.py /work/fresh_review_run.
Does not use outside data, and does not create prime dumps.
"""
from pathlib import Path
import json, sys, os, subprocess, hashlib
P='/usr/bin/python3.10'
G='/usr/bin/g++'
PY=[P,'-B','-u']
OLD=['portfolio_check','mertens_new','prefix','ramDus','mertensDus','ray_check','secondary_check','refine','extra_check','audit_summaries','mertens_check']
SPEC={'prefix':['portfolio_check.py','--qrh-free-prefix'],'ramDus':['portfolio_check.py','--dusart-only'],'mertensDus':['mertens_new.py','--dusart-only']}
NEW={'d02ram':'repair_r_results.txt','d02m':'repair_m_results.txt','d02secondary':'repair_secondary_results.txt','endpoint_check':'repair_endpoint_results.txt','repair_limits':'repair_limits_results.txt'}
MATCH={name+'.stdout':t for name,t in {
'finite26':'finite26.txt','finite20b':'finite20b.txt','finite100m':'finite100m.txt','mertens_check':'mertens_results.txt',
'old-007':'D01__SUBMITTED_008.txt','old-005':'D01_M_REVIEW_older24.stdout','portfolio_check':'ram_replay.txt',
'ramDus':'ram_dusart_replay.txt','mertens_new':'mertens_replay.txt','mertensDus':'mertens_dusart_replay.txt','prefix':'prefix_replay.txt'
}.items()}
MATCH.update({name+'_repair_replay.out':t for name,t in NEW.items()})
MATCH['d02finite_replay.out']='repair_tape.txt'
def main(root):
    root.mkdir()
    exact=root/'exact'
    env={**os.environ,'LC_ALL':'C','PYTHONPATH':str(exact)}
    env.pop('PYTHONOPTIMIZE',None)
    subprocess.run([P,'/task/RESTORE_CANDIDATE.py','--out',str(exact)],env=env,check=True)
    def run(name,cmd,stdout=None):
        with (root/(stdout or name+'.stdout')).open('wb') as a, (root/(name+'.stderr')).open('wb') as b:
            rc=subprocess.run(cmd,cwd=exact,env=env,stdout=a,stderr=b).returncode
        (root/(name+'.status')).write_text(str(rc)+'\n')
        if rc: raise RuntimeError((name,cmd,rc))
    exe=root/'d02finite_repair'
    run('current-cpp-compile',[G,'-O3','-std=c++17','d02finite_repair.cpp','-o',str(exe)])
    run('current-cpp',[str(exe)],'d02finite_replay.out')
    for name in NEW: run(name,PY+[name+'.py'],name+'_repair_replay.out')
    exe=root/'finite_opt'
    run('finite-opt-compile',[G,'-O3','-std=c++17','finite_opt.cpp','-o',str(exe)])
    for n,args in [('26',[]),('20b',['20000000000','200000']),('100m',['100000000','1000000'])]:
        run('finite'+n,[str(exe)]+args)
    for suf in ('007','005'):
        name='old-'+suf
        exe=root/name
        run(name+'-compile',[G,'-O3','-std=c++17','D01__SUBMITTED_'+suf+'.cpp','-o',str(exe)])
        run(name,[str(exe)])
    for p in OLD: run(p,PY+SPEC.get(p,[p+'.py']))
    path=Path(__file__).resolve().parent
    run('ancillary',[P,'-B',str(path/'ancillary.py'),str(root/'mertens_check.stdout')])
    for actual,expected in MATCH.items():
        a,b=(root/actual).read_bytes(),(exact/expected).read_bytes()
        assert a==b,(actual,expected)
        print(actual,expected,hashlib.sha256(a).hexdigest())
if __name__=='__main__': main(Path(sys.argv[1]).resolve())
