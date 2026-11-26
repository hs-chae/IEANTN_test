#!/usr/bin/env python3
"""Source-cold development compiler for the numerical source-verification cone."""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parents[2]
S=ROOT/'Solutions/RH080Next.v1/pv'
OLD=ROOT/'Solutions/RH080Study.v1/pv'
CTX=None
GENERIC=('Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets')
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,x):
    need(not p.exists(),'Freshreceipt required')
    t=p.with_name('.'+p.name+'.tmp')
    with t.open('x')as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--root',action='append',required=True);ap.add_argument('--context',type=Path,required=True);a=ap.parse_args();CTX=a.context
    need(not a.run.exists(),'Freshsourcecold rundirectory required');a.run.mkdir(parents=True)
    source=a.run/'source';objects=a.run/'objects';logs=a.run/'logs'
    for p in [source,objects,logs]:p.mkdir()
    c=json.loads(CTX.read_text());compiler=Path(c['compiler']);need(sha(compiler)==c['compiler_sha256'],'Compilerbytes differ')
    seen=set();active=set();rows=[]
    def visit(n):
        if n in seen or n.split('.')[0]in GENERIC:return
        need(n not in active,'Importcycle');active.add(n)
        p=next((q for base in [S/'lean',OLD/'lean',OLD.parent/'sine',ROOT/'Solutions/RH080Next.v1/explicit',ROOT/'Solutions/CH2.v6',ROOT/'Solutions/RH080Next.v1/primal',ROOT/'Solutions/RH080Next.v1/dual',ROOT]if(q:=base/(n.replace('.','/')+'.lean')).is_file()),None)
        need(p is not None,'Missingappsource '+n)
        imports=[]
        for line in p.read_text().splitlines():
            if line.startswith('import '):imports.extend(line[7:].split('--',1)[0].split())
        for d in imports:visit(d)
        active.remove(n);seen.add(n)
        target=source/(n.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes())
        rows.append(dict(module=n,origin=str(p),source_sha256=sha(p),snapshot=str(target),imports=imports))
    for n in a.root:visit(n)
    atomic(a.run/'PLAN.json',dict(status='FROZEN_SOURCE_COLD_DEVELOPMENT_PLAN_NOT_ACCEPTANCE',roots=a.root,source_rows=rows,context_sha256=sha(CTX),controller_sha256=sha(Path(__file__)),generic=c['generic_dependencies'],application_object_fallback=False))
    started=time.monotonic();commands=[]
    env=dict(os.environ,LEAN_PATH=str(objects)+':'+c['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
    for row in rows:
        n=row['module'];target=objects/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        out=logs/(n+'.stdout');err=logs/(n+'.stderr');tm=logs/(n+'.time');command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(256*2**30),'--stack='+str(256*2**20),'--',str(compiler),'-j2','--root='+str(source),'-o',str(target),row['snapshot']]
        t=time.monotonic()
        with out.open('xb')as o,err.open('xb')as e:p=subprocess.run(command,cwd=source,env=env,stdout=o,stderr=e)
        item=dict(module=n,command=command,exitcode=p.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm));commands.append(item)
        if p.returncode:
            atomic(a.run/'FAILED.json',dict(status='SOURCE_COLD_DEVELOPMENT_COMPILE_FAILED',commands=commands));raise ValueError('Compilefailed '+n)
        need(target.is_file(),'Noobjectoutput');item['object_sha256']=sha(target)
        atomic(a.run/(n+'.COMPILED.json'),item)
    for row in rows:need(sha(Path(row['origin']))==row['source_sha256'],'Sourceschangedduringdevelopment')
    atomic(a.run/'RESULT.json',dict(status='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY',roots=a.root,modules=len(rows),seconds=time.monotonic()-started,commands=commands,source_first_PV_complete=False,math_consumer_complete=False))
    print(json.dumps(dict(status='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY',modules=len(rows),seconds=time.monotonic()-started)))
if __name__=='__main__':main()
