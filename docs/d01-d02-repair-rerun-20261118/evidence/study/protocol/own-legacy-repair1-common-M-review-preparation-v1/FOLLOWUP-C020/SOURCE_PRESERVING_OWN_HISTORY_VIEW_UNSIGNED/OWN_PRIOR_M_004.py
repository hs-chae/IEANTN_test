# Run /usr/bin/python3.10 -B replay.py on the mounted task, with fresh /work/rv.
import subprocess as s, json, hashlib, os, time, concurrent.futures as cf
from pathlib import Path
root=Path('/work/rv'); root.mkdir()
py='/usr/bin/python3.10'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(label,cwd,args,src=(),stdin=None):
    t=time.monotonic()
    p=s.run(list(map(str,args)),cwd=cwd,input=stdin,capture_output=True,env=dict(os.environ,LC_ALL='C'))
    row=dict(label=label,cwd=str(cwd),argv=list(map(str,args)),stdin=None if stdin is None else stdin.decode(),
        sources={a:sha(cwd/a) for a in src},status=p.returncode,seconds=round(time.monotonic()-t,3),stdout=p.stdout.decode(),
        stderr=p.stderr.decode(),stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
    with open(root/(label+'.json'),'w') as f:json.dump(row,f,indent=2)
    return p
run('restore',root,[py,'/task/RESTORE_CANDIDATE.py','--out',root/'exact'])
ex=root/'exact'
run('restore_own',ex,[py,'RESTORE_OWN_HISTORY.py','--out',root/'own'],['RESTORE_OWN_HISTORY.py','OWN_HISTORY_INDEX.json'])
d1,d2=(root/'own'/d for d in ['D01','D02'])
def build(label,dir,fn,extra=()):
    out=root/label
    cpp=fn.endswith('.cpp')
    flags=['-O3']+(['-std=c++17','-pthread'] if cpp else [])
    p=run('build_'+label,dir,['/usr/bin/g++' if cpp else '/usr/bin/gcc',*flags,fn,'-o',out],[fn,*extra])
    assert p.returncode==0,label
    return out
ep=build('endpoint',d1,'endpoint.c')
si=build('sieve',d1,'sieve.c')
br=build('bridge',d2,'bridge.cpp',['count.cpp'])
co=build('count',d2,'count.cpp')
mf=build('mfinite',d2,'mfinite.cpp',['bridge.cpp','count.cpp'])
me=build('mexact',d2,'mexact.cpp',['mfinite.cpp','bridge.cpp','count.cpp'])
mc=build('m_coarse',ex,'m_coarse.cpp',['d02_bridge.cpp','d02_count.cpp'])
mo=build('m_onset',ex,'m_onset.cpp',['d02_mfinite.cpp','d02_bridge.cpp','d02_count.cpp'])
jobs=[]
def add(label,dir,args,src=()):jobs.append((label,dir,args,src))
for f in ['cert','ram','smooth','tails']:
    add('D01_'+f,d1,[py,'-B',f+'.py'],sorted({f+'.py','cert.py','weights.txt'}))
r=run('D01_endpoint',d1,[ep],[str(ep),'endpoint.c'])
(root/'endpoint.out').write_bytes(r.stdout)
add('D01_root',d1,[py,'-B','endpoint.py',root/'endpoint.out'],['cert.py','endpoint.py',str(root/'endpoint.out')])
for i,argv in enumerate(['1000 72004899338 2000 2000 2100 sqrt','1000 1318815735 2000 2000 2000 sqrt','240000 3500000 500 500 500','3500000 13000000 199 199 230','13000000 50000000 130 130 170','50000000 1318815735 100 100 150']):
    add('D01_sieve'+str(i),d1,[si,*argv.split()],[str(si),'sieve.c'])
for i,(a,b) in enumerate(zip([38358837683,46063982972,53769128262,61474273551,69179418841,76884564131,84589709420,92294854710],[46063982972,53769128262,61474273551,69179418841,76884564131,84589709420,92294854710,100000000000])):
    add('D02_bridge'+str(i),d2,[br,a,b],[str(br),'bridge.cpp','count.cpp'])
add('D02_analytic',d2,[py,'-B','analytic.py',co],['analytic.py','count.cpp',str(co)])
add('D02_mcheck',d2,[py,'-B','mcheck.py'],['mcheck.py','analytic.py'])
for i,argv in enumerate(['2278381750 2278382 20000','2278381950 3500000 19998','3500000000 5000000 18000','5000000000 18100000 16000','w 912561000 2278383 29998','100000000 100 18100000','1500000000 60 111000000','2500000000 50 181000000','10000000000 30 1125000000','10000000000 11 4200000000 8000000']):
    b=me if i<=4 else mf
    add('D02_m'+str(i),d2,[b,*argv.split()],[str(b),'mexact.cpp','mfinite.cpp','bridge.cpp','count.cpp'])
for label,argv in [('tp5','2278381730 2278382 20000'),('tp6','2278381940 3500000 19998')]:
    add(label,d2,[me,*argv.split()],[str(me),'mexact.cpp','mfinite.cpp','bridge.cpp','count.cpp'])
for label,argv in [('tw2','w 912560000 2278383 2999999'),('tw5','w 912559998 2278383 3000000'),('tw4','w 912559995 2278383 3000000')]:
    add(label,ex,[mo,*argv.split()],[str(mo),'m_onset.cpp','d02_mfinite.cpp','d02_bridge.cpp','d02_count.cpp'])
for k,argv in enumerate(['9000000000 1100 3000000000 5000000','11500000000 1000 4760000000 10000000','13000000000 900 8500000000 7000000','18000000000 800 12000000000 6000000','26500000000 700 16000000000 5000000','35500000000 600 22000000000 5500000','61000000000 500 30000000000 5000000']):
    add('coarse'+str(k),ex,[mc,*argv.split()],[str(mc),'m_coarse.cpp','d02_bridge.cpp','d02_count.cpp'])
for fn in ['ram_repair.py','m_repair.py']:
    add(fn[:-3],ex,[py,'-B',fn],sorted({fn,'ram_repair.py','d01_cert.py','d01_weights.txt'}))
# Non-asserted exploration, also replayed to document insufficient tests.
for label,argv in [('m10','12000000000 10 4760000000 8000000'),('m09','13000000000 9 5500000000 8000000')]:
    add(label,d2,[mf,*argv.split()],[str(mf),'mfinite.cpp','bridge.cpp','count.cpp'])
add('tw',d2,[me,'w',912560000,2278383,29999],[str(me),'mexact.cpp','mfinite.cpp','bridge.cpp','count.cpp'])
for label,argv in [('tw3','w 912559999 2278383 3000000'),('tr1','2278381900 3500000 1999800'),('tr2','2278381750 3500000 2000000'),('tr3','2278381950 3500000 1999800'),('tr4','2278381950 3500000 2000000')]:
    add(label,ex,[mo,*argv.split()],[str(mo),'m_onset.cpp','d02_mfinite.cpp','d02_bridge.cpp','d02_count.cpp'])
with cf.ThreadPoolExecutor(max_workers=4) as t:
    futures=[t.submit(run,*a) for a in jobs]
    for a,j in zip(jobs,futures):print(a[0],j.result().returncode,flush=True)
