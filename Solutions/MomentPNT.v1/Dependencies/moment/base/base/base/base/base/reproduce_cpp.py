from pathlib import Path
import argparse,hashlib,json,subprocess,time
B=Path(__file__).resolve().parent
def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--compiler',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh external output');out.mkdir(parents=True);pin=json.loads((B/'CPP_ASSOCIATION_PIN.json').read_text());need(sha(a.compiler)==pin['compiler_sha256'],'compiler identity');tree=B/'height-bundle-source-v3';need({p.name:sha(p)for p in tree.iterdir()if p.is_file()}==pin['physical_C_files'],'source identity');binary=out/'height-program';raw=out/'output.bin';commands=[];start=time.monotonic()
 for command,name,target in [([str(a.compiler),*pin['compiler_flags'],str(tree/'height_bundle.cpp'),'-o',str(binary)],'compile',out/'compile.stdout'),([str(binary)],'run',raw)]:
  with target.open('wb')as so,(out/(name+'.stderr')).open('wb')as se:q=subprocess.run(command,stdout=so,stderr=se)
  need(q.returncode==0,name+' failed');commands.append(command)
 need(sha(raw)==pin['expected_output_sha256'],'original exact output mismatch');binary_sha=sha(binary);need(binary.parent==out and not binary.is_symlink(),'owned binary identity');binary.unlink();r={'status':'RAW_ACTUAL_CPP_OUTPUT_ASSOCIATION_PASS','seconds':time.monotonic()-start,'commands':commands,'output_sha256':sha(raw),'binary_sha256':binary_sha,'verified_regenerable_binary_removed':True,'source_first_PV':False,'qualification':'Raw association only; no source execution or ANT theorem inferred.'};(out/'RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
if __name__=='__main__':main()
