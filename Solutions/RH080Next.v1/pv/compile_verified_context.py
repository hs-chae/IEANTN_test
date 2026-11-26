#!/usr/bin/env python3
"""Development compiler importing only source/hash/receipt-associated objects.
This is not a full source-cold final replay or a whole-PV acceptance validator.
"""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
    need(not p.exists(),'Fresh receipt required');tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x')as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()
def imports(p):
    return[n for line in p.read_text().splitlines()if line.startswith('import ')for n in line[7:].split('--',1)[0].split()]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path,required=True);ap.add_argument('--bank',action='append',type=Path,required=True)
    ap.add_argument('--module',required=True);ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--memory-gib',type=int,default=256);a=ap.parse_args()
    need(1<=a.memory_gib<=300,'Per-run allowance at most 300GiB')
    mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable']>=(a.memory_gib+256)*2**30,'Insufficient available memory after 256GiB host reserve')
    need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    for s in ['source','objects']: (a.run/s).mkdir()
    c=json.loads(a.context.read_text());need(sha(Path(c['compiler']))==c['compiler_sha256'],'Pinned compiler mismatch')
    index={}
    for bank in a.bank:
        plan=json.loads((bank/'PLAN.json').read_text())
        need(plan['context_sha256']==sha(a.context),'Bank has another dependency context')
        rows=plan.get('source_rows',[dict(module=plan.get('module'),origin=plan.get('source_origin'),snapshot=str(bank/'source'/(plan.get('module','').replace('.','/')+'.lean')),source_sha256=plan.get('source_sha256'))])
        for row in rows:
            n=row['module'];receipt=bank/(n+'.COMPILED.json')
            if not receipt.is_file():
                receipt=bank/'RESULT.json'
                if not receipt.is_file():continue
                result=json.loads(receipt.read_text())
                if result.get('module')!=n:continue
            else:result=json.loads(receipt.read_text())
            if result.get('exitcode')!=0:continue
            obj=bank/'objects'/(n.replace('.','/')+'.olean')
            if not obj.is_file():continue
            index.setdefault(n,[]).append((row,receipt,result,obj))
        # Imported objects copied by an earlier source-associated module build
        # retain their own original compiler receipts and exact source snapshots.
        for item in plan.get('accepted_dependencies',[]):
            if not all(k in item for k in ['source_origin','snapshot','receipt','receipt_sha256']):continue
            n=item['module'];receipt=Path(item['receipt']);obj=bank/'objects'/(n.replace('.','/')+'.olean')
            need(receipt.is_file()and sha(receipt)==item['receipt_sha256'],'Transitive receipt changed')
            result=json.loads(receipt.read_text())
            if result.get('exitcode')!=0 or not obj.is_file():continue
            need(sha(obj)==item['object_sha256']==result['object_sha256'],'Transitive copied object changed')
            row=dict(module=n,origin=item['source_origin'],snapshot=item['snapshot'],source_sha256=item['source_sha256'])
            index.setdefault(n,[]).append((row,receipt,result,obj))
    selected={};active=set();dependencies=[]
    def dep(n):
        if n in selected or n.split('.')[0]in GENERIC:return
        need(n not in active,'Import cycle');active.add(n);found=None
        for row,receipt,result,obj in index.get(n,[]):
            origin=Path(row['origin']);snapshot=Path(row['snapshot'])
            if origin.is_file()and snapshot.is_file()and sha(origin)==sha(snapshot)==row['source_sha256']and sha(obj)==result['object_sha256']:
                found=(row,receipt,result,obj);break
        need(found is not None,'No source-associated compiled dependency '+n)
        row,receipt,result,obj=found
        for child in imports(Path(row['origin'])):dep(child)
        target=a.run/'objects'/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(obj.read_bytes())
        selected[n]=row;active.remove(n)
        dependencies.append(dict(module=n,source_origin=row['origin'],source_sha256=row['source_sha256'],snapshot=row['snapshot'],object_sha256=sha(target),receipt=str(receipt),receipt_sha256=sha(receipt)))
    project=Path(__file__).resolve().parent.parent
    relative=a.module.replace('.','/')+'.lean'
    candidates=[base/relative for base in [project/'pv/lean',project/'explicit',project/'primal',project/'dual'] if (base/relative).is_file()]
    need(len(candidates)==1,'Root source must resolve uniquely in pinned RH080Next source directories: '+a.module)
    original=candidates[0]
    for n in imports(original):dep(n)
    target=a.run/'source'/(a.module.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(original.read_bytes())
    obj=a.run/'objects'/(a.module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    (a.run/'controller.py').write_bytes(Path(__file__).read_bytes())
    save(a.run/'PLAN.json',dict(status='SOURCE_ASSOCIATED_DEVELOPMENT_ONLY',module=a.module,source_origin=str(original),source_sha256=sha(original),accepted_dependencies=dependencies,context_sha256=sha(a.context),controller_sha256=sha(Path(__file__)),application_fallback=False))
    env=dict(os.environ,LEAN_PATH=str(a.run/'objects')+':'+c['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
    command=['/usr/bin/time','-v','-o',str(a.run/'compile.time'),'prlimit','--as='+str(a.memory_gib*2**30),'--stack='+str(256*2**20),'--',c['compiler'],'-j2','--root='+str(a.run/'source'),'-o',str(obj),str(target)]
    start=time.monotonic()
    with(a.run/'stdout').open('xb')as out,(a.run/'stderr').open('xb')as err:p=subprocess.run(command,cwd=a.run/'source',env=env,stdout=out,stderr=err)
    result=dict(status='PASS_SOURCE_ASSOCIATED_MODULE_ONLY'if p.returncode==0 else'FAILED_SOURCE_ASSOCIATED_MODULE',module=a.module,exitcode=p.returncode,seconds=time.monotonic()-start,command=command,source_sha256=sha(target),stdout_sha256=sha(a.run/'stdout'),stderr_sha256=sha(a.run/'stderr'),resource_receipt_sha256=sha(a.run/'compile.time'),whole_source_PV_complete=False)
    need(sha(original)==sha(target),'Root source changed during compilation')
    for row in dependencies:need(sha(Path(row['source_origin']))==row['source_sha256'],'Dependency source changed')
    if p.returncode==0:result['object_sha256']=sha(obj)
    save(a.run/'RESULT.json',result);print(json.dumps({k:result[k]for k in ['status','module','exitcode','seconds']}));need(p.returncode==0,'Compile failed; logs preserved')
if __name__=='__main__':main()
