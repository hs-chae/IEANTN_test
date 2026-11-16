"""Fresh application-source proof rebuild with only pinned public libraries."""
import argparse, concurrent.futures, hashlib, json, os, re, subprocess, time
from pathlib import Path

BASE = Path(__file__).resolve().parent

def require(value,message):
    if not value:
        raise ValueError(message)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def atomic(path,value):
    temp=path.with_suffix('.pending')
    temp.write_text(json.dumps(value,indent=2)+'\n')
    os.replace(temp,path)

def no_admitted_proof(stdout,stderr,name):
    text=stdout+stderr
    require(not any(fragment in text for fragment in
        ["declaration uses 'sorry'",'declaration uses `sorry`','sorryAx','Lean.ofReduceBool']),
        'admitted/native proof diagnostic in '+name)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--environment',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=1)
    ap.add_argument('--check-source-only',action='store_true')
    ap.add_argument('--point-jobs',type=int,default=1)
    a=ap.parse_args()
    require(1<=a.jobs<=8,'jobs1..8; caller must reserve actual host resources')
    require(1<=a.point_jobs<=a.jobs,'point jobs1..jobs')
    lock_path=BASE/'SOURCE_LOCK.json'
    lock=json.loads(lock_path.read_text())
    require(len(lock['sources'])==1412 and len(lock['payloads'])==574 and len(lock['roots'])==2350,'exact frozen composition population')
    names={r['module'] for r in lock['sources']}
    require(len(names)==1412 and len(set(lock['roots']))==2350,'unique source/root identities')
    require(all(set(r['imports'])<=names for r in lock['sources']),'complete application source closure')
    for row in lock['sources']+lock['payloads']:
        p=BASE/row['path']
        require(p.is_file() and not p.is_symlink() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'source/payload pin '+row['path'])
    if a.check_source_only:
        out=a.out.resolve()
        require(not out.exists() and BASE not in out.parents,'fresh source-only output outside capsule')
        out.mkdir(parents=True)
        receipt=dict(status='PASS_INPUT_IDENTITIES_ONLY_NOT_COMBINED_LEAN_REPLAY',source_modules=1412,payloads=574,theorem_roots=2350,source_lock_sha256=sha(lock_path),combined_fresh_replay_completed=False)
        atomic(out/'RECEIPT.json',receipt)
        print(json.dumps(receipt))
        return
    require(a.environment is not None and a.environment.is_file(),'public generic environment required for actual Lean replay')
    e=json.loads(a.environment.read_text())
    tool=Path(e['compiler']).parent.parent
    def runtime_check():
        for r in lock['runtime_pins']['toolchain_files']:
            p=tool/r['path']
            require(p.is_file()and p.stat().st_size==r['bytes']and sha(p)==r['sha256'],'runtime/kernel pin '+r['path'])
        q=subprocess.run([e['compiler'],'--version'],capture_output=True,text=True,check=True)
        require(q.stdout.strip()==lock['runtime_pins']['lean_version'],'kernel version mismatch')
    runtime_check()
    require(sha(Path(e['compiler']))==lock['compiler_sha256'],'compiler pin mismatch')
    deps=e['generic_dependencies']
    require([{k:d[k]for k in ['name','commit','url']}for d in deps]==lock['generic_dependencies'],'generic dependency population')
    for d in deps:
        q=subprocess.run(['git','-C',d['source'],'rev-parse','HEAD'],capture_output=True,text=True,check=True)
        require(q.stdout.strip()==d['commit'],'generic source pin '+d['name'])
        require(Path(d['objects']).is_dir(),'generic objects missing '+d['name'])
    out=a.out.resolve()
    require(not out.exists()and BASE not in out.parents,'fresh output outside source capsule')
    out.mkdir(parents=True)
    objects=out/'objects';objects.mkdir()
    logs=out/'logs';logs.mkdir()
    def source_check():
        for r in lock['sources']+lock['payloads']:
            p=BASE/r['path']
            require(p.is_file()and not p.is_symlink()and p.stat().st_size==r['bytes']and sha(p)==r['sha256'],'source/payload pin '+r['path'])
    source_check()
    env=os.environ.copy()
    env['LEAN_PATH']=':'.join([str(objects)]+[d['objects']for d in deps])
    env['LEAN_NUM_THREADS']='1'
    records=[];start=time.monotonic()
    def execute(name,cmd):
        so=logs/(name+'.stdout');se=logs/(name+'.stderr');tm=logs/(name+'.time');t=time.monotonic()
        with so.open('w')as f,se.open('w')as g:
            q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],stdout=f,stderr=g,cwd=BASE,env=env)
        row=dict(name=name,command=cmd,exit_code=q.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(so),stderr_sha256=sha(se),time_sha256=sha(tm))
        require(q.returncode==0,'failed '+name)
        no_admitted_proof(so.read_text(),se.read_text(),name)
        return row
    def compile(row):
        obj=objects/Path(row['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        r=execute(row['module'],[e['compiler'],'-j1','-R',str(BASE/'source'),str(BASE/row['path']),'-o',str(obj)])
        r['object_sha256']=sha(obj)
        return r
    pending={r['module']:r for r in lock['sources']};done=set();running={}
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as ex:
            while pending or running:
                ready=[n for n,r in pending.items()if set(r['imports'])<=done]
                # Point normalization is measured separately from generic source
                # compilation. Explicit point-jobs permits justified larger runs.
                for n in ready:
                    if len(running)>=a.jobs:break
                    if n.startswith('SourceHeightPointsV2.Point') and sum(v.startswith('SourceHeightPointsV2.Point') for v in running.values())>=a.point_jobs:continue
                    running[ex.submit(compile,pending.pop(n))]=n
                require(bool(running),'cycle/missing dependency')
                completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
                for f in completed:
                    n=running.pop(f);records.append(f.result());done.add(n)
                    atomic(out/'PROGRESS.json',dict(completed=len(done),total=len(lock['sources']),seconds=time.monotonic()-start))
        audit=out/'Audit.lean'
        audit.write_text(''.join('import '+n+'\n'for n in lock['root_modules'])+'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nrun_elab do\n let env ← getEnv\n for n in (['+','.join('`'+n for n in lock['roots'])+'] : List Name) do\n  let some ci := env.find? n | throwError "missing {n}"\n  let ax ← Lean.collectAxioms n\n  logInfo m!"BODY_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n')
        records.append(execute('audit',[e['compiler'],'-j1','-R',str(out),str(audit)]))
        rows=[json.loads(x.split('BODY_AUDIT ',1)[1])for x in(logs/'audit.stdout').read_text().splitlines()if'BODY_AUDIT 'in x]
        require([x['name']for x in rows]==lock['roots'],'audit population mismatch')
        require(all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}for x in rows),'nonstandard axiom')
        source_check();runtime_check()
    except Exception as ex:
        atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED',error=str(ex),records=records,seconds=time.monotonic()-start))
        raise
    result=dict(status='PASS_SOURCE_COLD_BARE768_C_POINT_TO_ANT_COMPOSITION',source_lock_sha256=sha(lock_path),reproducer_sha256=sha(Path(__file__)),source_modules=len(lock['sources']),payloads=len(lock['payloads']),theorem_roots=len(rows),records=records,audits=rows,elapsed_seconds=time.monotonic()-start,application_object_inputs=[],combined_fresh_replay_completed=True,full_program_source_first_PV=False,namespace_isolated=False,actual_C_execution_repeated=False,qualification=lock['qualification'])
    atomic(out/'RECEIPT.json',result)
    print(json.dumps({k:result[k]for k in ['status','source_modules','payloads','theorem_roots','elapsed_seconds']}))

if __name__=='__main__':
    main()
