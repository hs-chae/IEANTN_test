#!/usr/bin/env python3
"""Prepare an isolated genuine Comparator Lake package; no verification receipt."""
from pathlib import Path
import argparse,json,hashlib,shutil,re,os
H=Path(__file__).resolve().parent;I=H.parent;S=I.parent;R=S.parents[1]
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh comparison source namespace');out.mkdir(parents=True);core=out/'network';core.mkdir();rows=[]
 for name in ['IEANTN','Tools','scripts']:shutil.copytree(R/name,core/name,ignore=shutil.ignore_patterns('__pycache__'))
 for name in ['IEANTN.lean','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copyfile(R/name,core/name)
 (core/'.lake').mkdir();(core/'.lake/packages').symlink_to((R/'.lake/packages').resolve(),target_is_directory=True)
 manifests=[];pm=read(I/'corrected/capture/SOURCE_CLOSURE.json')
 manifests += [R/x['path']for x in pm['baseline_manifests']]
 manifests += [I/'corrected/capture/SOURCE_CLOSURE.json',I/'supplement/audit-corrected-capture/SOURCE_CLOSURE.json',S/'box/zero/cold-capture/SOURCE_CLOSURE.json',H/'capture/SOURCE_CLOSURE.json'];modules={}
 for m in manifests:
  for q in read(m)['modules']:
   need(q['module']not in modules,'module namespace collision');need(sha(R/q['path'])==q['sha256'],'source freeze');modules[q['module']]=q
 need(len(modules)==693,'exact693 source map')
 selected=set();node_ids=sorted({'.'.join(x.split('.')[:2]) for x in read(H/'capture/SOURCE_CLOSURE.json')['final_roots']});need(len(node_ids)==19,'exact19 proved nodes from55 frozen canonical roots')
 targets=['Public'+n.split('.')[0]+n.split('.')[1].upper()for n in node_ids];need(all(n in modules for n in targets),'actual canonical public module inventory')
 def visit(m):
  if m in selected:return
  selected.add(m)
  for dep in modules[m].get('application_imports',[]):
   need(dep in modules,'complete application map:'+dep);visit(dep)
 for m in targets:visit(m)
 actual=[m for m in selected if not m.startswith('IEANTN.')and not m.startswith('Public')];package=core/'Solutions/RHOcticPushProofs';package.mkdir(parents=True)
 for m in sorted(actual):
  q=modules[m];src=R/q['path'];dest=package/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes());rows.append({'module':m,'source':q['path'],'sha256':q['sha256'],'destination':str(dest.relative_to(out))})
  for inc in re.findall(r'include_str\s+"([^"\n]+)"',src.read_text()):
   origin=(src.parent/inc).resolve();payload=(dest.parent/inc).resolve();need(origin.is_relative_to(R)and origin.is_file()and payload.is_relative_to(package),'include payload');payload.parent.mkdir(parents=True,exist_ok=True)
   if payload.exists():need(sha(payload)==sha(origin),'payload collision')
   else:payload.write_bytes(origin.read_bytes())
   rows.append({'resource':str(origin.relative_to(R)),'sha256':sha(origin),'destination':str(payload.relative_to(out))})
 (package/'lakefile.toml').write_text('name = "RHOcticPushProofs"\ndefaultTargets = ["VerifiedProofs"]\n\n[[require]]\nname = "IEANTN"\npath = "../.."\n\n[[lean_lib]]\nname = "VerifiedProofs"\nroots = '+json.dumps(sorted(actual))+'\n')
 shutil.copyfile(R/'lean-toolchain',package/'lean-toolchain')
 # First bounded test: the complete no-argument exact Mellin node, all3 claims.
 node='BoxMellinInputs.v2';d=core/'Solutions'/node;d.mkdir();shutil.copyfile(R/'Solutions'/node/'Solution.lean',d/'Solution.lean');shutil.copyfile(R/'lean-toolchain',d/'lean-toolchain');(d/'lakefile.toml').write_text('name = "solution_BoxMellinInputs_v2"\ndefaultTargets = ["Solution"]\n\n[[require]]\nname = "IEANTN"\npath = "../.."\n\n[[require]]\nname = "RHOcticPushProofs"\npath = "../RHOcticPushProofs"\n\n[[lean_lib]]\nname = "Solution"\nroots = ["Solution"]\n')
 names=['BoxMellinInputs.v2.challenge_'+x for x in ['first_moment','second_moment_identity','stieltjes_trapezoid']];config={'challenge_module':'IEANTN.Nodes.BoxMellinInputs.v2.Challenge','solution_module':'Solution','theorem_names':names,'permitted_axioms':['propext','Quot.sound','Classical.choice'],'enable_nanoda':True};(d/'comparator.json').write_text(json.dumps(config,indent=2)+'\n')
 for path in sorted(core.rglob('*')):
  if path.is_file()and not path.is_symlink()and '.lake'not in path.relative_to(core).parts:
   rows.append({'sourcefile':str(path.relative_to(out)),'sha256':sha(path)})
 (out/'SOURCE_PACKAGE.json').write_text(json.dumps({'status':'PREPARED_NOT_COMPARATOR_ACCEPTED','controller_sha256':sha(Path(__file__)),'pinned_source_modules':693,'selected_public_modules':len(targets),'selected_proof_nodes':node_ids,'selection':'Exact19node identities owning all55 frozen canonical proof roots; excludes3 explicit literature nodes and unrelated Public-prefixed helpers','proof_package_modules':len(actual),'bounded_test_node':node,'copied_application_objects':False,'core_source':str(core),'rows':rows},indent=2)+'\n');print('proofpackage',len(actual),'publictargets',len(targets))
if __name__=='__main__':main()
