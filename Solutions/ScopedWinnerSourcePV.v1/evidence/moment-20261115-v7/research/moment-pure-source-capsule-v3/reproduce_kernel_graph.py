"""Fresh application-source proof rebuild with only pinned public libraries."""
import argparse, concurrent.futures, hashlib, json, math, os, re, subprocess, time
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

def parse_strict(text):
    def pairs(rows):
        result={}
        for key,value in rows:
            require(key not in result,'duplicateJSON '+key)
            result[key]=value
        return result
    def invalid(value):
        raise ValueError('nonfiniteJSON '+value)
    def floating(value):
        result=float(value)
        require(math.isfinite(result),'overflowJSON')
        return result
    return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=invalid)

def schema_check(lock):
    sources=lock['sources'];payloads=lock['payloads']
    modules=[r['module']for r in sources];paths=[r['path']for r in sources]
    require(len(sources)==565 and len(modules)==len(set(modules)) and len(paths)==len(set(paths)),
            'unique complete565source/module identities')
    extra=[r['path']for r in payloads]
    require(len(extra)==len(set(extra)) and not(set(paths)&set(extra)),'unique disjoint payload paths')
    roots=lock['roots'];rootmods=lock['root_modules']
    require(len(roots)==1124 and len(roots)==len(set(roots)),'unique complete1124roots')
    require(len(rootmods)==len(set(rootmods)) and set(rootmods)<=set(modules),'unique known rootmodules')
    public=lock['public_import_modules']
    allowed=('Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph',
             'LeanSearchClient','Plausible','Lean','Std','Init')
    require(len(public)==len(set(public)) and all(n.split('.')[0]in allowed for n in public),
            'known pinned public generic module prefixes')
    for row in sources:
        module=row['module'];path=Path(row['path'])
        require(re.fullmatch(r'[\w.]+',module)is not None and
                all(part not in{'','..'}for part in module.split('.')) and
                path==Path('source')/Path(module.replace('.','/')).with_suffix('.lean'),
                'canonical exact source/module path')
        actual=[]
        for line in(BASE/path).read_text().splitlines():
            match=re.match(r'^(?:public )?import\s+(.+)',line)
            if match:actual+=match.group(1).split('--',1)[0].split()
        require(all(n in modules or n in public for n in actual),'unknown import '+module)
        require(row['imports']==[n for n in actual if n in modules],
                'complete actual application import edges '+module)
    return set(modules)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--environment',type=Path)
    ap.add_argument('--check-inputs-only',action='store_true')
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=2)
    a=ap.parse_args()
    require(1<=a.jobs<=12,'jobs1..12')
    lock=parse_strict((BASE/'SOURCE_LOCK.json').read_text())
    allmodules=schema_check(lock)
    if a.check_inputs_only:
        for row in lock['sources']+lock['payloads']:
            p=BASE/row['path']
            require(p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'strict source identity')
        output=a.out.resolve()
        require(not output.exists()and BASE not in output.parents,'fresh checkoutput')
        output.mkdir(parents=True)
        atomic(output/'RECEIPT.json',dict(status='PURE565_SOURCE_IDENTITIES_ONLY_NOT_A_PROOF_REPLAY',source_modules=len(lock['sources']),application_object_inputs=[]))
        return
    require(a.environment is not None and a.environment.is_file(),'public generic environment required')
    e=parse_strict(a.environment.read_text())
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
        require(not any(t in so.read_text()+se.read_text() for t in ['sorryAx','Lean.ofReduceBool',"declaration uses 'sorry'",'declaration uses `sorry`']),'unproved/native diagnostic '+name)
        return row
    def compile(row):
        obj=objects/Path(row['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        r=execute(row['module'],[e['compiler'],'-j1','-R',str(BASE/'source'),str(BASE/row['path']),'-o',str(obj)])
        r['object_sha256']=sha(obj)
        return r
    pending={r['module']:r for r in lock['sources']};done=set();running={}
    require(len(pending)==len(lock['sources']),'no source-module collapse')
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as ex:
            while pending or running:
                ready=[n for n,r in pending.items()if set(r['imports'])<=done]
                for n in ready[:a.jobs-len(running)]:
                    running[ex.submit(compile,pending.pop(n))]=n
                require(bool(running),'cycle/missing dependency')
                completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
                for f in completed:
                    n=running.pop(f);records.append(f.result());done.add(n)
                    atomic(out/'PROGRESS.json',dict(completed=len(done),total=len(lock['sources']),seconds=time.monotonic()-start))
        require(done==allmodules and len(records)==len(lock['sources']) and
                {r['name']for r in records}==allmodules,'all565actual source executions completed')
        audit=out/'Audit.lean'
        audittext=''.join('import '+n+'\n'for n in lock['root_modules'])+'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
        for begin in range(0,len(lock['roots']),64):
            audittext+='run_elab do\n let env ← getEnv\n for n in (['+','.join('`'+n for n in lock['roots'][begin:begin+64])+'] : List Name) do\n  let some ci := env.find? n | throwError "missing {n}"\n  let ax ← Lean.collectAxioms n\n  logInfo m!"BODY_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n'
        audit.write_text(audittext)
        records.append(execute('audit',[e['compiler'],'-j1','-R',str(out),str(audit)]))
        rows=[parse_strict(x.split('BODY_AUDIT ',1)[1])for x in(logs/'audit.stdout').read_text().splitlines()if'BODY_AUDIT 'in x]
        require([x['name']for x in rows]==lock['roots'],'audit population mismatch')
        require(all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}for x in rows),'nonstandard axiom')
        require(len(records)==len(lock['sources'])+1 and len({r['name']for r in records})==len(records),
                'exact source/audit execution population')
        source_check();runtime_check()
    except Exception as ex:
        atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED',error=str(ex),records=records,seconds=time.monotonic()-start))
        raise
    result=dict(status='PASS_PURE_MOMENT_PNT_SOURCE_COLD_EMPTY_BANK',source_lock_sha256=sha(BASE/'SOURCE_LOCK.json'),reproducer_sha256=sha(Path(__file__)),source_modules=len(lock['sources']),payloads=len(lock['payloads']),theorem_roots=len(rows),records=records,audits=rows,elapsed_seconds=time.monotonic()-start,application_object_inputs=[],namespace_isolated=False,actual_C_execution_repeated=False,qualification=lock['qualification'])
    atomic(out/'RECEIPT.json',result)
    print(json.dumps({k:result[k]for k in ['status','source_modules','payloads','theorem_roots','elapsed_seconds']}))

if __name__=='__main__':
    main()
