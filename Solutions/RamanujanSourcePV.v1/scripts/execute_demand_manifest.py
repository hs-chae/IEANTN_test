#!/usr/bin/env python3
"""Reproduce generated certificate compilation with explicit source/log checks.

This is a scoped host kernel-check pipeline. Its result is not a namespace
isolation receipt and is not by itself source-first C program verification.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,os,re,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
STD3={'propext','Classical.choice','Quot.sound'}
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):
    def pairs(items):
        result={}
        for k,v in items:need(k not in result,'duplicate JSON key');result[k]=v
        return result
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def publish(p,data):
    tmp=p.with_name(p.name+'.pending');need(not tmp.exists(),'fresh atomic stage')
    with tmp.open('x')as f:json.dump(data,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    tmp.replace(p)
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--manifest',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--jobs',type=int,default=2);ap.add_argument('--memory-gib',type=int,default=48);ap.add_argument('--cpus',default='0,1,2,3');a=ap.parse_args()
    need(1<=a.jobs<=4,'bounded initial proof workers');manifest=a.manifest.resolve();d=read(manifest);need(d['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','exact proposal schema/status')
    source_root=Path(d['source_root']).resolve();modules=d['modules'];names=[m['module']for m in modules];need(len(names)==len(set(names)),'unique compiler module identities')
    sources=[Path(m['source']).resolve()for m in modules];need(len(sources)==len(set(sources)),'unique written source identities')
    actual=sorted(p.resolve()for p in source_root.rglob('*.lean'));need(sorted(sources)==actual,'complete generated Lean source population')
    for m,p in zip(modules,sources):need(p.is_relative_to(source_root)and not p.is_symlink()and p.is_file()and sha(p)==m['sha256'],'exact generated source '+m['module'])
    need(sha(d['packed_file'])==d['packed_sha256'],'exact complete generated record data')
    out=a.out.resolve();need(not out.exists(),'fresh owned execution output');out.mkdir(parents=True);logs=out/'logs';logs.mkdir();audit=out/'audit';context=read(S/'BUILD_CONTEXT.json');objects=Path(context['new_application_object_root']);compiler_hash=sha(context['compiler']);source_code=sha(S/'RamanujanPV/QuotientCertificateCode.lean');started=time.monotonic()
    by_name={m['module']:m for m in modules};done=set();pending=set(names);records=[];active={}
    def compile_one(name):
        m=by_name[name];source=Path(m['source']);need(sha(source)==m['sha256'],'source unchanged before compiler')
        cmd=[sys.executable,str(S/'scripts/compile_lean.py'),name,'--source-root',str(source_root),'--audit-root',str(audit),'--memory-gib',str(a.memory_gib),'--cpus',a.cpus]
        t=time.monotonic();result=subprocess.run(cmd,capture_output=True,text=True);stdout=logs/(name+'.stdout');stderr=logs/(name+'.stderr');stdout.write_text(result.stdout);stderr.write_text(result.stderr);need(result.returncode==0,'Lean compilation failed '+name+'; preserved '+str(stdout))
        receipt=read(json.loads(result.stdout.strip().splitlines()[-1])['audit']+'/RUN.json');need(receipt['status']=='COMPILED'and receipt['source_sha256']==m['sha256']and receipt['compiler_sha256']==compiler_hash,'actual source/compiler receipt '+name)
        actual_audit=Path(json.loads(result.stdout.strip().splitlines()[-1])['audit']);proof_log=(actual_audit/'stdout').read_text();error_log=(actual_audit/'stderr').read_text();need(not any(x in proof_log+error_log for x in ['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'forbidden proof trust leaf '+name)
        requested=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',source.read_text(),re.M)
        for short in requested:
            full=short if '.'in short else d['namespace']+'.'+short
            no=re.search(r"'"+re.escape(full)+r"' does not depend on any axioms",proof_log)
            ax=re.search(r"'"+re.escape(full)+r"' depends on axioms:\s*\[([^\]]*)\]",proof_log,re.S)
            need(no is not None or ax is not None,'missing actual named axiom report '+full)
            found=set()if no else{v.strip()for v in ax[1].split(',')if v.strip()}
            need(found<=STD3,'nonstandard theorem axioms '+full)
            if m['kind']=='check':need(not found,'numerical checker theorem must be axiom-free '+full)
        obj=objects/Path(*name.split('.')).with_suffix('.olean');need(obj.is_file()and sha(obj)==receipt['object_sha256'],'actual compiled object '+name)
        need(sha(source)==m['sha256']and sha(S/'RamanujanPV/QuotientCertificateCode.lean')==source_code,'scientific source unchanged after compiler')
        return {'module':name,'source_sha256':m['sha256'],'object_sha256':sha(obj),'compiler_receipt':str(actual_audit/'RUN.json'),'compiler_receipt_sha256':sha(actual_audit/'RUN.json'),'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'seconds':time.monotonic()-t,'requested_axiom_reports':requested}
    with ThreadPoolExecutor(max_workers=a.jobs)as pool:
        while pending or active:
            for name in sorted(pending):
                if len(active)>=a.jobs:break
                deps={x for x in by_name[name]['dependencies']if x in by_name}
                if deps<=done:active[pool.submit(compile_one,name)]=name;pending.remove(name)
            need(active,'cyclic or incomplete generated dependency graph')
            ready,_=wait(active,return_when=FIRST_COMPLETED)
            for future in ready:
                name=active.pop(future);record=future.result();records.append(record);done.add(name)
                publish(out/'PROGRESS.json',{'status':'RUNNING_OR_PARTIAL_NOT_FINAL_ACCEPTANCE','completed':len(done),'total':len(names),'last_module':name,'records':records})
    need(done==set(names)and d['final_module']in done,'complete exact generated universe including final mathematical consumer')
    publish(out/'RESULT.json',{'status':'COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV','manifest':str(manifest),'manifest_sha256':sha(manifest),'certificate_code_sha256':source_code,'compiler_sha256':compiler_hash,'results':d['results'],'source_modules':len(names),'seconds':time.monotonic()-started,'records':records,'remaining_boundaries':'Separate actual C source/AST/typed execution/driver composition and final clean isolated closure must be supplied; no completed finite Ramanujan theorem is claimed here.'})
    print(json.dumps({'status':'COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV','results':d['results'],'modules':len(names),'seconds':time.monotonic()-started,'out':str(out)},indent=2))
if __name__=='__main__':main()
