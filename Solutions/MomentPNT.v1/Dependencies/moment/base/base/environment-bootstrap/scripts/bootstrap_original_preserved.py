#!/usr/bin/env python3
"""Fetch exact public dependencies into an experiment-owned fresh environment."""
from pathlib import Path, PurePosixPath
import argparse,datetime,hashlib,json,math,os,platform,subprocess,tarfile,urllib.request
from runtime_identity import check_runtime

ROOT=Path(__file__).resolve().parents[1]

def need(ok,msg):
    if not ok:raise ValueError(msg)

def pairs(items):
    d={}
    for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
    return d

def load(p):
    def finite(s):
        v=float(s);need(math.isfinite(v),'nonfinite JSON number');return v
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_float=finite,
        parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for b in iter(lambda:f.read(1024**2),b''):h.update(b)
    return h.hexdigest()

def run(cmd,cwd,env,log):
    with log.open('ab')as f:
        f.write((json.dumps(cmd)+'\n').encode());f.flush()
        subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)

def download(url,p,want,size):
    if p.exists():
        need(p.stat().st_size==size and sha(p)==want,'existing asset identity');return
    tmp=p.with_name(p.name+'.partial')
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IEANTN-Reproduction/1.0'}),timeout=60)as r,tmp.open('wb')as f:
        while True:
            b=r.read(1024**2)
            if not b:break
            f.write(b)
    need(tmp.stat().st_size==size and sha(tmp)==want,'official asset hash mismatch')
    tmp.rename(p)

def main():
    a=argparse.ArgumentParser();a.add_argument('--work',type=Path,required=True);a.add_argument('--receipt',type=Path,required=True);a.add_argument('--resume',action='store_true');o=a.parse_args()
    lock=load(ROOT/'ENVIRONMENT.lock.json');work=o.work.absolute()
    need(work.resolve()==work,'canonical work path required')
    if work.exists():need(o.resume and (work/'OWNED_REPRODUCTION_WORK.json').exists(),'fresh owned work required')
    else:
        work.mkdir(parents=True);(work/'OWNED_REPRODUCTION_WORK.json').write_text(json.dumps(dict(owner='IEANTN_REPRODUCIBILITY_20261109',environment_lock_sha256=sha(ROOT/'ENVIRONMENT.lock.json')),indent=2)+'\n')
    need(not o.receipt.exists(),'fresh receipt required')
    asset=lock['lean_asset'];p=work/asset['name'];want=asset['digest'].removeprefix('sha256:')
    download(asset['browser_download_url'],p,want,asset['size'])
    toolchain=work/asset['name'].removesuffix('.tar.zst')
    log=work/'bootstrap.log'
    if not toolchain.exists():
        names=subprocess.check_output(['tar','--zstd','-tf',str(p)],text=True).splitlines()
        need(all(not PurePosixPath(n).is_absolute() and '..'not in PurePosixPath(n).parts for n in names),'unsafe official archive path')
        run(['tar','--zstd','--extract','--file',str(p),'--directory',str(work),'--no-same-owner'],work,os.environ.copy(),log)
    compiler=toolchain/'bin/lean';need(sha(compiler)==lock['compiler_sha256'],'exact pinned compiler bytes required')
    runtime=check_runtime(toolchain)
    env=os.environ.copy()
    for key in ['LEAN_PATH','LEAN_SRC_PATH','ELAN_TOOLCHAIN','LAKE_HOME']:env.pop(key,None)
    env.update(PATH=str(toolchain/'bin')+os.pathsep+env.get('PATH',''),LEAN_SYSROOT=str(toolchain),MATHLIB_CACHE_DIR=str(work/'mathlib-download-cache'))
    packages={p['name']:p for p in lock['packages']};mathlib=work/'mathlib'
    if not mathlib.exists():
        mathlib.mkdir();run(['git','init','--quiet'],mathlib,env,log)
        run(['git','remote','add','origin',packages['mathlib']['url']],mathlib,env,log)
        run(['git','fetch','--depth=1','origin',packages['mathlib']['rev']],mathlib,env,log)
        run(['git','-c','advice.detachedHead=false','checkout','--detach','FETCH_HEAD'],mathlib,env,log)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()
    need(head==packages['mathlib']['rev'],'pinned mathlib commit required')
    run([str(toolchain/'bin/lake'),'exe','cache','get'],mathlib,env,log)
    dependencies=[]
    for name in ['batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']:
        source=mathlib if name=='mathlib' else mathlib/'.lake/packages'/name
        head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()
        need(head==packages[name]['rev'],'dependency commit mismatch '+name)
        objects=source/'.lake/build/lib/lean';need(objects.is_dir(),'generic dependency cache missing '+name)
        dependencies.append(dict(name=name,url=packages[name]['url'],commit=head,source=str(source),objects=str(objects),target='/evaldeps/'+name))
    test=work/'ImportSmoke.lean';test.write_text('import Mathlib\n#check Real.exp_pos\n#check Nat.Prime\n')
    smoke_env=dict(env,LEAN_PATH=os.pathsep.join(d['objects']for d in dependencies))
    run([str(compiler),str(test)],work,smoke_env,log)
    receipt=dict(schema=1,status='CLEAN_PUBLIC_PINNED_ENVIRONMENT_READY',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),work=str(work),toolchain=str(toolchain),compiler=str(compiler),compiler_sha256=sha(compiler),compiler_version=subprocess.check_output([str(compiler),'--version'],text=True).strip(),lean_archive_sha256=sha(p),generic_dependencies=dependencies,lock_sha256=sha(ROOT/'ENVIRONMENT.lock.json'),bootstrap_script_sha256=sha(Path(__file__)),system=dict(platform=platform.platform(),python=platform.python_version()),old_experiment_paths_used=False,project_objects_reused=False,cache_source='public pinned Mathlib cache; build relevant experiment and common modules fresh',bootstrap_log_sha256=sha(log))
    receipt['actual_runtime_identity']=runtime
    (work/'ENVIRONMENT.json').write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n')
    o.receipt.parent.mkdir(parents=True,exist_ok=True);o.receipt.write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(status=receipt['status'],environment=str(work/'ENVIRONMENT.json'),compiler_sha256=receipt['compiler_sha256'])))

if __name__=='__main__':main()
