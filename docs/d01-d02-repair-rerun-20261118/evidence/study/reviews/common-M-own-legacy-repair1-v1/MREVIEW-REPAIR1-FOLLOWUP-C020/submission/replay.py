import os, sys, json, subprocess as sp, hashlib as h
from pathlib import Path
p='/usr/bin/python3.10'; env={**os.environ,'LC_ALL':'C'}
out=Path(sys.argv[2]) if len(sys.argv)>2 else Path('/work/submission')
cwd=Path(os.environ.get('REVIEW_RESTORED','/work/exact'))
def run(tag,*args,stdin=None):
 args=list(map(str,args))
 wd=cwd if cwd.exists() else cwd.parent
 q=sp.run(args,cwd=wd,env=env,input=None if stdin is None else stdin.encode(),stdout=sp.PIPE,stderr=sp.PIPE)
 receipt=dict(tag=tag,argv=args,cwd=str(wd),stdin=stdin,status=q.returncode)
 for k,b in [('stdout',q.stdout),('stderr',q.stderr)]:
  receipt[k]=b.decode(errors='replace'); receipt[k+'_sha256']=h.sha256(b).hexdigest()
 with (out/('replay_'+sys.argv[1]+'.jsonl')).open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(tag,q.returncode,flush=True)
 return q.stdout
group=sys.argv[1]
if group=='setup':
 idx=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
 for r in idx['sources']:
  for k in ['pdf','text']:assert h.sha256((Path(idx['root'])/r[k]).read_bytes()).hexdigest()==r[k+'_sha256']
 run('restore',p,'/task/RESTORE_CANDIDATE.py','--out',cwd)
 for alias,orig in [('cert.py','d01_cert.py'),('analytic.py','d02_analytic.py'),('weights.txt','d01_weights.txt')]:
  a=cwd/alias
  if not a.exists():a.symlink_to(orig)
 for f in ['d01_endpoint','d01_sieve']:run(f,'/usr/bin/gcc','-O3',f+'.c','-o',f)
 for f in ['d02_bridge','d02_count','d02_mexact','d02_mfinite','m_coarse','m_onset']:run(f,'/usr/bin/g++','-O3','-std=c++17','-pthread',f+'.cpp','-o',f)
if group=='ram':
 for f in ['ram_repair','ram_high','d01_ram']:
  run(f,p,'-B',f+'.py')
if group=='analytic':
 for f in ['m_repair','m_postreview','d01_cert','d01_tails','d01_smooth','d02_mcheck','d02_analytic']:
  run(f,p,'-B',f+'.py',*(['./d02_count'] if f=='d02_analytic' else []))
if group=='original_pdf':
 run('PT-finiteRH-p4-layout',p,'-B',str(Path(__file__).resolve().with_name('source_layout.py')))
if group=='failed_tests':
 run('failed_tests',p,'-B',str(Path(__file__).resolve().with_name('failed_tests.py')))
if group=='checks':
 run('source-rounding',p,'-B',str(Path(__file__).resolve().with_name('proof_checks.py')))
if group=='sign':
 b=run('local-count','./d01_endpoint'); (cwd/'root.out').write_bytes(b)
 run('root',p,'-B','d01_endpoint.py','root.out')
 ep=[38358837683,46063982972,53769128262,61474273551,69179418841,76884564131,84589709420,92294854710,100000000000]
 for i,(a,b) in enumerate(zip(ep,ep[1:])):run('bridge'+str(i),'./d02_bridge',a,b)
if group=='smallfinite':
 for args in [(1000,72004899338,2000,2000,2100,'sqrt'),(1000,1318815735,2000,2000,2000,'sqrt'),(240000,3500000,500,500,500),(3500000,13000000,199,199,230),(13000000,50000000,130,130,170),(50000000,1318815735,100,100,150)]:
  run('sieve','./d01_sieve',*args)
if group=='early':
 for args in [(2278381730,2278382,20000),(2278381940,3500000,19998),(3500000000,5000000,18000),(5000000000,18100000,16000),('w',912561000,2278383,29998)]:
  run('exact','./d02_mexact',*args)
 for args in [(912559998,2278383,3000000),(912560000,2278383,2999999)]:
  run('weighted','./m_onset','w',*args)
 for args in [(100000000,100,18100000,40000),(1500000000,60,111000000,40000),(2500000000,50,181000000,40000),(10000000000,30,1125000000,40000),(10000000000,11,4200000000,8000000)]:
  run('early','./d02_mfinite',*args)
batches={'coarse1':[(9000000000,1100,3200000000,18000000),(9000000000,1100,3000000000,5000000),(11500000000,1000,4760000000,10000000),(13000000000,900,8500000000,7000000),(18000000000,800,12000000000,6000000),(26500000000,700,16000000000,5000000),(35500000000,600,22000000000,5500000),(61000000000,500,30000000000,5000000)],'coarse2':[(90000000000,400,35000000000,10000000),(170000000000,300,90000000000,12000000),(290000000000,240,140000000000,16000000),(90000000000,400,50000000000,9000000)]}
for args in batches.get(group,[]):run('coarse','./m_coarse',*args)
