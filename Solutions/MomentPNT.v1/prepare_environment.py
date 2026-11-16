"""Locate only the pinned public compiler and eight generic dependencies."""
from pathlib import Path
import argparse,json,hashlib,subprocess,os,tempfile,importlib.util
P=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--toolchain',type=Path,required=True)
 ap.add_argument('--mathlib',type=Path,required=True);ap.add_argument('--packages',type=Path,required=True)
 ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();spec=importlib.util.spec_from_file_location('strict_reproduction',P/'reproduce.py');reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader);pin=reader.read(P/'PINNED_ENVIRONMENT.json')
 tool=a.toolchain.resolve();compiler=tool/'bin/lean';need(sha(compiler)==pin['compiler_sha256'],'Pinned compiler')
 for name,h in pin['runtime_files'].items():need(sha(tool/name)==h,'Pinned kernel/runtime '+name)
 deps=[]
 for row in pin['dependencies']:
  source=a.mathlib.resolve()if row['name']=='mathlib'else a.packages.resolve()/row['name']
  q=subprocess.run(['git','-C',str(source),'rev-parse','HEAD'],capture_output=True,text=True)
  need(q.returncode==0 and q.stdout.strip()==row['commit'],'Pinned public source '+row['name'])
  objects=source/'.lake/build/lib/lean';need(objects.is_dir(),'Public generic objects '+row['name'])
  deps.append({**row,'source':str(source),'objects':str(objects),'target':'/evaldeps/'+row['name']})
 result={'compiler':str(compiler),'compiler_sha256':pin['compiler_sha256'],'generic_dependencies':deps,
  'qualification':'Only pinned public generic libraries; no application object paths accepted.'}
 out=a.out.resolve();need(not out.exists(),'Fresh environment destination');out.parent.mkdir(parents=True,exist_ok=True)
 fd,tmp=tempfile.mkstemp(dir=out.parent,prefix='.'+out.name)
 with os.fdopen(fd,'w')as f:json.dump(result,f,indent=2);f.write('\n')
 os.replace(tmp,out);print(out)
if __name__=='__main__':main()
