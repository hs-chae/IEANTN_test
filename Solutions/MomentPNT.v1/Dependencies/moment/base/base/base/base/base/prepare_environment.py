"""Record only the exact pinned public dependencies used by this component."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
B=Path(__file__).resolve().parent
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--toolchain',type=Path,required=True)
    ap.add_argument('--mathlib',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    T=a.toolchain.resolve();M=a.mathlib.resolve();out=a.out.resolve();lock=json.loads((B/'SOURCE_LOCK.json').read_text())
    need(not out.exists()and B not in out.parents,'fresh environment output outside source capsule')
    need(sha(T/'bin/lean')==lock['compiler_sha256'],'compiler pin')
    for r in lock['runtime_pins']['toolchain_files']:
        p=T/r['path'];need(p.is_file()and p.stat().st_size==r['bytes']and sha(p)==r['sha256'],'runtime pin '+r['path'])
    q=subprocess.run([str(T/'bin/lean'),'--version'],capture_output=True,text=True,check=True)
    need(q.stdout.strip()==lock['runtime_pins']['lean_version'],'Lean kernel identity')
    rows=[]
    for r in lock['generic_dependencies']:
        root=M if r['name']=='mathlib'else M/'.lake/packages'/r['name']
        q=subprocess.run(['git','-C',str(root),'rev-parse','HEAD'],capture_output=True,text=True,check=True)
        need(q.stdout.strip()==r['commit'],'public source pin '+r['name'])
        obj=root/'.lake/build/lib/lean';need(obj.is_dir(),'missing public library cache '+r['name'])
        rows.append(dict(r,source=str(root),objects=str(obj)))
    result=dict(schema='POSITIVE6_STDIO_PUBLIC_GENERIC_ENV_V1',compiler=str(T/'bin/lean'),generic_dependencies=rows,
                qualification='Only pinned public generic compiler/libraries; no previous application object paths.')
    out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.pending');tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,out)
    print(json.dumps(dict(status='PINNED_PUBLIC_GENERIC_ENVIRONMENT_WRITTEN',generic_libraries=len(rows),application_object_paths=0)))
if __name__=='__main__':main()
