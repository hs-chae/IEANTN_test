#!/usr/bin/env python3
"""Rebuild the three actual canonical signed-node consumers from pinned source.

The signed18/Mobius7 input banks must be outputs of the original source-only
replayers. Every source/object/command/audit is checked; only recorded objects
are copied into a fresh library. Mathematical source assumptions remain explicit.
This kernel replay is not source-first PV or an official Comparator receipt.
"""
from pathlib import Path
import argparse,hashlib,json,math,os,re,shutil,subprocess,sys,time

PIN_SHA='cd4c8fe46b27f1073e5b816e33e846018f482367066a6c1adce9b2dc92c8703c'
ALLOWED={'propext','Classical.choice','Quot.sound'}
PYFLAGS={0:[],1:['-O'],2:['-OO']}[sys.flags.optimize]
HEADER='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(rows):
  o={}
  for k,v in rows:need(k not in o,'duplicate JSON key:'+k);o[k]=v
  return o
 def finite(raw):
  value=float(raw);need(math.isfinite(value),'nonfinite/overflow JSON float');return value
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def publish(p,d):
 tmp=p.with_name('.'+p.name+'.pending');tmp.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');os.replace(tmp,p)
def audits(text,expected):
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
 need(len(rows)==len(set(x[0]for x in rows))==len(expected),'complete distinct axiom audit count')
 need({x[0]for x in rows}==set(expected),'exact axiom audit identities')
 result=[]
 for name,raw in rows:
  axioms={x.strip()for x in raw.split(',')if x.strip()};need(axioms<=ALLOWED,'nonstandard axiom:'+name)
  result.append({'theorem':name,'axioms':sorted(axioms)})
 return result

def bank_check(network,root,spec,pins,context):
 base=network/spec['base'];m=read(base/'SOURCE_MANIFEST.json');census=read(base/'THEOREM_CENSUS.json')
 for name,h in spec['files'].items():need(sha(base/name)==h,'bank original source pin:'+spec['label']+':'+name)
 need(root.is_dir()and not root.is_symlink(),'regular supplied bank directory required')
 rp=root/'REPLAY_RESULT.json';need(rp.is_file()and not rp.is_symlink(),'supplied bank receipt missing/symlink')
 r=read(rp)
 need(r['schema']==spec['schema']and r['status']==spec['status'],'supplied bank receipt status/schema')
 need(r['compiler_sha256']==pins['compiler_sha256']and r['source_manifest_sha256']==spec['files']['SOURCE_MANIFEST.json'],'bank compiler/manifest identity')
 need(r['native_execution_axioms']is False and r['old_application_objects_used']is False and r['only_pinned_generic_libraries_used']is True,'bank source-only/native trust flags')
 need(r['source_first_PV']is False and r['official_Comparator_receipt']is False,'bank verification tier')
 need(type(r['python_optimization'])is int and r['python_optimization']in [0,1,2],'bank optimization mode')
 expected=m['modules'];commands=r['commands'];need(len(expected)==len(commands)==spec['count'],'bank complete child routes')
 need([x['module']for x in commands]==[x['module']for x in expected],'bank module order and identity')
 want=set();objects=[]
 for source,run in zip(expected,commands):
  mod=source['module'];need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',mod)is not None,'invalid bank module')
  rel=Path(mod.replace('.','/')+'.olean');want.add(rel.as_posix());obj=root/'objects'/rel;src=root/source['path']
  need(obj.is_file()and not obj.is_symlink()and src.is_file()and not src.is_symlink(),'bank regular source/object file')
  need(type(run['returncode'])is int and run['returncode']==0,'bank recorded compiler failure')
  need(run['source_sha256']==source['sha256']==sha(src)==sha(base/source['path']),'bank source byte identity:'+mod)
  need(re.fullmatch('[0-9a-f]{64}',run['object_sha256'])is not None and sha(obj)==run['object_sha256'],'bank object byte identity:'+mod)
  cmd=run['command'];need(isinstance(cmd,list)and len(cmd)==6 and all(isinstance(x,str)for x in cmd),'bank recorded command syntax')
  need(cmd[1]=='-R'and cmd[3]=='-o'and Path(cmd[0]).name=='lean','bank actual compiler command')
  need(Path(cmd[5]).relative_to(Path(cmd[2])).as_posix()==mod.replace('.','/')+'.lean','bank command source route')
  need(Path(cmd[4]).relative_to(Path(cmd[2]).parent/'objects').as_posix()==rel.as_posix(),'bank command output route')
  objects.append({'module':mod,'relative':rel.as_posix(),'path':str(obj),'sha256':run['object_sha256']})
 actual={p.relative_to(root/'objects').as_posix()for p in(root/'objects').rglob('*')if p.is_file()}
 need(actual==want,'bank unexpected/missing object or sidecar')
 expected_theorems=[x['declaration']for x in census];log=root/'logs'/f"{spec['audit_module']}.stdout"
 aa=audits(log.read_text(),expected_theorems)
 mode=['normal','O','OO'][sys.flags.optimize]
 cmd=[sys.executable,*PYFLAGS,str(base/'reproduce.py'),'--context',str(context),'--optimize',mode,'--check']
 check=subprocess.run(cmd,capture_output=True,text=True)
 need(check.returncode==0,'original bank source/compiler/context preflight failed:'+check.stderr[-1600:])
 return {'label':spec['label'],'receipt':str(rp),'receipt_sha256':sha(rp),'source_manifest_sha256':sha(base/'SOURCE_MANIFEST.json'),'source_preflight':cmd,'audits':aa,'objects':objects}


def main():
 p=argparse.ArgumentParser(allow_abbrev=False,description=__doc__)
 for name in ['network','signed-run','mobius-run','context','out']:p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--check',action='store_true',help='Check all inputs only, without creating output or compiling new modules.')
 a=p.parse_args();network=a.network.resolve();out=a.out.resolve();context=a.context.resolve();pins_path=Path(__file__).with_name('SIGNED_NODE_REPLAY_PINS.json');own_hash=sha(__file__)
 need(sha(pins_path)==PIN_SHA,'replay pin manifest identity');pins=read(pins_path);need(pins['schema']=='SIGNED_CANONICAL_SOURCE_AND_BANK_PINS_V1','pin schema');need(not out.exists(),'fresh output required')
 need(network.is_dir()and context.is_file(),'network/context path missing');ctx=read(context)
 need(ctx['compiler_sha256']==pins['compiler_sha256']==sha(ctx['compiler']),'compiler identity')
 need([{'name':d['name'],'revision':d['revision']}for d in ctx['generic_dependencies']]==pins['generic_dependencies'],'exact generic source identities')
 need(len(ctx['generic_libraries'])==8,'eight generic library routes')
 for row in pins['files']+pins['sources']:
  need(sha(network/row['path'])==row['sha256'],'canonical/helper source pin:'+row['path'])
  if 'historical_alias'in row:need(sha(network/row['historical_alias'])==row['sha256'],'actual Solution differs from recorded Canonical alias')
 banks=[bank_check(network,a.signed_run.resolve(),pins['banks'][0],pins,context),bank_check(network,a.mobius_run.resolve(),pins['banks'][1],pins,context)]
 print('PASS_PINNED_SOURCES_AND_ALL25_RECORDED_SOURCE_OBJECTS',flush=True)
 if a.check:return
 out.mkdir(parents=True);src=out/'source';src.mkdir();deps=out/'input-objects';deps.mkdir();start=time.monotonic()
 source_records=[]
 for row in pins['sources']:
  dest=src/(row['module'].replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(network/row['path'],dest);need(sha(dest)==row['sha256'],'copied canonical source changed');source_records.append({**row,'copied':str(dest)})
 for bank in banks:
  for row in bank['objects']:
   dest=deps/row['relative'];dest.parent.mkdir(parents=True,exist_ok=True)
   need(not dest.exists(),'supplied bank object collision');shutil.copyfile(row['path'],dest);need(sha(dest)==row['sha256'],'copied bank object differs')
 typed=[
  ('nicolas_log','RH.v1.hypothesis → Nicolas.v1.spectral_bound → Nicolas.v1.log_f_upper_full → Nicolas.v1.log_product_lower',pins['targets'][0]),
  ('nicolas_relative','RH.v1.hypothesis → Nicolas.v1.spectral_bound → Nicolas.v1.log_f_upper_full → Nicolas.v1.relative_product_lower',pins['targets'][1]),
  ('mertens_cube','RH.v1.hypothesis → MertensRH.v1.bfknw154 → MertensRH.v1.bfknw21 → Buthe.v1.theorem_2_psi → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → MertensRH.v1.positive_cube',pins['targets'][2]),
  ('mertens_earlier','RH.v1.hypothesis → MertensRH.v1.bfknw154 → MertensRH.v1.bfknw21 → Buthe.v1.theorem_2_psi → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → MertensRH.v1.positive_earlier',pins['targets'][3]),
  ('mertens_profile','RH.v1.hypothesis → MertensRH.v1.bfknw154 → MertensRH.v1.bfknw21 → Buthe.v1.theorem_2_psi → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → MertensRH.v1.cube_profile',pins['targets'][4]),
  ('mobius_weighted','MobiusRH.v1.power_bound → MobiusRH.v1.abel_source → MobiusRH.v1.weighted_bound',pins['targets'][5])]
 lines=[HEADER,'import CanonicalNicolas','import CanonicalMertensRH','import CanonicalMobiusRH','namespace SignedNodeReplayTyped']
 for name,t,target in typed:lines.append(f'theorem {name} : {t} := @{target}')
 lines.extend(['end SignedNodeReplayTyped','set_option pp.universes false'])
 for target in pins['targets']:lines.extend([f'#check @{target}',f'#print axioms {target}'])
 (src/'SignedNodesAudit.lean').write_text('\n'.join(lines)+'\n')
 modules=[x['module']for x in pins['sources']]+['SignedNodesAudit'];helper=network/'Solutions/RHContinuation.v1/scripts/build_modules.py';cmd=[sys.executable,*PYFLAGS,str(helper),'--source',str(src),'--out',str(out/'build'),'--extra-library',str(deps)]
 for mod in modules:cmd.extend(['--module',mod])
 env=os.environ.copy();env['IEANTN_GENERIC_CONTEXT']=str(context)
 with(out/'build.stdout').open('w')as stdout,(out/'build.stderr').open('w')as stderr:
  built=subprocess.run(cmd,env=env,stdout=stdout,stderr=stderr)
 need(built.returncode==0,'canonical compilation failed; preserve output/build logs')
 result=read(out/'build/BUILD.json');need(result['status']=='PASS'and[x['module']for x in result['modules']]==modules,'complete actual build routes')
 for row in result['modules']:
  need(type(row['returncode'])is int and row['returncode']==0 and sha(out/'build/objects'/(row['module'].replace('.','/')+'.olean'))==row['object_sha256'],'actual compiled output identity')
 log=(out/'build/logs/SignedNodesAudit.stdout').read_text();aa=audits(log,pins['targets'])
 for target in pins['targets']:need(re.search(r'\b'+re.escape(target)+r'\b',log)is not None,'typed theorem output missing')
 for row in pins['sources']+pins['files']:need(sha(network/row['path'])==row['sha256'],'original canonical/helper source changed during compilation')
 for bank in banks:
  need(sha(bank['receipt'])==bank['receipt_sha256'],'bank receipt changed during compilation')
  for row in bank['objects']:need(sha(row['path'])==row['sha256'],'bank object changed during compilation')
 need(sha(__file__)==own_hash and sha(pins_path)==PIN_SHA,'reproducer/pins changed during execution')
 receipt={'schema':'CANONICAL_SIGNED_NODE_SOURCE_REPLAY_V1','status':'PASS_THREE_CANONICAL_SIGNED_NODES_SIX_TYPED_OUTPUTS','python_optimization':sys.flags.optimize,'elapsed_seconds':time.monotonic()-start,'controller_sha256':own_hash,'pins_sha256':PIN_SHA,'compiler_sha256':pins['compiler_sha256'],'context_sha256':sha(context),'sources':source_records,'supplied_banks':banks,'command':cmd,'build_receipt_sha256':sha(out/'build/BUILD.json'),'audits':aa,'exact_typed_consumers':typed,'output_modules':modules,'source_first_PV':False,'official_Comparator_receipt':False,'mathematical_status':'Actual six conditional transport theorems; Nicolas/Mertens source predicates remain explicit; Mobius power_bound and Abel source remain hypotheses. No RH-to-M proof is claimed.','trust_boundary':'Uses only recorded, source/object/audit-checked banks freshly generated by the original18/7 replayers, pinned compiler and supplied pinned generic context. The receipt is a local reproducibility record, not external authentication of arbitrary supplied files.'}
 publish(out/'RESULT.json',receipt);print(receipt['status'],flush=True)

if __name__=='__main__':main()
