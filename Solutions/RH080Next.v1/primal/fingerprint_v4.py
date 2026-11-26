#!/usr/bin/env python3
"""Run the genuine structural hash algorithm with scoped imports and bounded Lean.

Only the import frontend differs from Tools/Hash.lean. Its entire fingerprint
algorithm body is byte-identical, and all nine preserved v3 hashes must reproduce
before the official Python fingerprint writer may generate the two v4 files.
This is metadata generation, not a mathematical proof or Comparator receipt.
"""
import argparse,hashlib,importlib.util,json,os,subprocess,sys,time
from pathlib import Path

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);here=Path(__file__).resolve().parent;repo=here.parents[2];c=json.loads(a.context.read_text());need(sha(Path(c['compiler']))==c['compiler_sha256'],'Compiler hash differs');source=a.out/'source';objects=a.out/'objects';source.mkdir();objects.mkdir();env=dict(os.environ,LEAN_PATH=str(objects.resolve())+':'+c['generic_lean_path']);began=time.monotonic()
 mods=['IEANTN.Vocabulary.CMSFunctional']+[f'IEANTN.Nodes.{family}.v{version}.Conclusions'for family in ['GaussianFourierWitness','RHAsymptoticGaussian']for version in [3,4]];rows=[]
 for name in mods:
  original=repo/(name.replace('.','/')+'.lean');frozen=source/(name.replace('.','/')+'.lean');frozen.parent.mkdir(parents=True,exist_ok=True);frozen.write_bytes(original.read_bytes());o=objects/(name.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True);cmd=[c['compiler'],'-j','1','--root='+str(source.resolve()),'-o',str(o.resolve()),str(frozen.resolve())];r=subprocess.run(cmd,env=env,text=True,capture_output=True);(a.out/(name.replace('.','_')+'.stdout')).write_text(r.stdout);(a.out/(name.replace('.','_')+'.stderr')).write_text(r.stderr);need(r.returncode==0,'Scoped input compilation failed '+name);rows.append({'module':name,'source_sha256':sha(original),'object_sha256':sha(o),'command':cmd})
 original=repo/'Tools/Hash.lean';text=original.read_text();node_mods=mods[1:];need(text.count('import IEANTN\n')==1,'Hash frontend changed');text=text.replace('import IEANTN\n',''.join('import '+name+'\n'for name in node_mods),1);old='let env ← importModules #[{ module := `IEANTN }] {}';new='let env ← importModules #['+','.join('{ module := `'+name+' }'for name in node_mods)+'] {}';need(text.count(old)==1,'Dynamic import frontend changed');text=text.replace(old,new,1)
 def algorithm(body):return body.split('namespace IEANTN.Fingerprint\n',1)[1].split('end IEANTN.Fingerprint',1)[0]
 need(algorithm(text)==algorithm(original.read_text()),'Structural algorithm body differs');frontend=source/'ScopedHash.lean';frontend.write_text(text)
 spec=importlib.util.spec_from_file_location('ieantn_official',repo/'scripts/ieantn.py');tool=importlib.util.module_from_spec(spec);spec.loader.exec_module(tool);all_nodes=tool.load_nodes();wanted={f'{family}.v{version}'for family in ['GaussianFourierWitness','RHAsymptoticGaussian']for version in [3,4]};nodes={k:v for k,v in all_nodes.items()if k in wanted};need(set(nodes)==wanted,'Expected exactly four source nodes');tool.load_nodes=lambda:nodes;run=subprocess.run
 def scoped_run(command,**kwargs):
  need(command[:3]==['lake','exe','ieantn_hash'],'Unexpected tool subprocess')
  kwargs['env']=env;return run([c['compiler'],'-j','1','--run',str(frontend.resolve()),*command[3:]],**kwargs)
 tool.subprocess.run=scoped_run
 current=tool.compute_fingerprints();old_checks=[]
 for family in ['GaussianFourierWitness','RHAsymptoticGaussian']:
  p=repo/'IEANTN/Nodes'/family/'v3/fingerprints.json';expected=json.loads(p.read_text())
  for name,digest in expected.items():need(current.get(name)==digest,'Preserved v3 structural hash differs '+name);old_checks.append(name)
 need(len(old_checks)==9,'Expected nine v3 control conclusions');tool.compute_fingerprints=lambda:current;need(tool.fingerprint(False),'Official writer failed')
 for row in rows:need(sha(repo/(row['module'].replace('.','/')+'.lean'))==row['source_sha256'],'Source changed during fingerprint')
 result={'status':'PASS_OFFICIAL_STRUCTURAL_ALGORITHM_SCOPED_IMPORTS_AND_NINE_V3_CONTROLS','scope':'Exact official Tools/Hash.lean algorithm and scripts/ieantn.py writer; only imports narrowed to the four named nodes. No all-network hash coverage claim.','tool_source_sha256':sha(original),'scoped_frontend_sha256':sha(frontend),'algorithm_body_sha256':hashlib.sha256(algorithm(text).encode()).hexdigest(),'python_writer_sha256':sha(repo/'scripts/ieantn.py'),'compiler_sha256':c['compiler_sha256'],'source_modules':rows,'v3_controls':old_checks,'v4_fingerprints':{name:digest for name,digest in current.items()if '.v4.'in name},'seconds':time.monotonic()-began};p=a.out/'RESULT.pending';p.write_text(json.dumps(result,indent=2)+'\n');os.link(p,a.out/'RESULT.json');p.unlink();print(json.dumps({'status':result['status'],'seconds':result['seconds']}))
if __name__=='__main__':main()
