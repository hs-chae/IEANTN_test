#!/usr/bin/env python3
"""Actual CLI rejection controls and three sequential canonical-node builds.

All mutations affect disposable copied fixtures only. No assert/__debug__ gate.
Each subprocess inherits a48GiB address-space bound, keeping one proof job active.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time

B=Path(__file__).resolve().parent

def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 for name in ['network','signed-run','mobius-run','context','out']:p.add_argument('--'+name,type=Path,required=True)
 a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls output');out.mkdir(parents=True);start=time.monotonic();pins=json.loads((B/'SIGNED_NODE_REPLAY_PINS.json').read_text());network=a.network.resolve();records=[]
 fixture=out/'fixture';fixture.mkdir();testnet=fixture/'network';testnet.mkdir()
 shutil.copytree(network/'Solutions/RHContinuation.v1/signed',testnet/'Solutions/RHContinuation.v1/signed')
 for row in pins['files']+pins['sources']:
  dest=testnet/row['path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(network/row['path'],dest)
 signed=fixture/'signed';mobius=fixture/'mobius';shutil.copytree(a.signed_run,signed);shutil.copytree(a.mobius_run,mobius);context=fixture/'context.json';shutil.copyfile(a.context,context)
 fixture_identity={q.relative_to(fixture).as_posix():{'sha256':sha(q),'bytes':q.stat().st_size}for q in fixture.rglob('*')if q.is_file()}
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
 def run(mode,name,expected,check=True,extra=None):
  target=out/f'mode-{mode}'/name;target.parent.mkdir(exist_ok=True);flags={0:[],1:['-O'],2:['-OO']}[mode]
  cmd=['prlimit','--as=51539607552','--',sys.executable,*flags,str(B/'reproduce_signed_nodes.py'),'--network',str(testnet),'--signed-run',str(signed),'--mobius-run',str(mobius),'--context',str(context),'--out',str(target)]
  if check:cmd.append('--check')
  if extra:cmd+=extra
  st=time.monotonic();r=subprocess.run(cmd,env=env,capture_output=True,text=True);logs=out/'control-logs';logs.mkdir(exist_ok=True);stem=logs/f'{mode}-{name}';Path(str(stem)+'.stdout').write_text(r.stdout);Path(str(stem)+'.stderr').write_text(r.stderr)
  need((r.returncode==0)==expected,'unexpected actual CLI acceptance:'+str(mode)+':'+name+':'+r.stderr[-1000:])
  if not expected:need(not(target/'RESULT.json').exists(),'negative case published success:'+name)
  if expected and not check:
   receipt=json.loads((target/'RESULT.json').read_text());need(receipt['status']=='PASS_THREE_CANONICAL_SIGNED_NODES_SIX_TYPED_OUTPUTS'and receipt['python_optimization']==mode,'full build status/mode')
  records.append({'mode':mode,'case':name,'expected_accept':expected,'returncode':r.returncode,'seconds':time.monotonic()-st,'command':cmd,'stdout_sha256':sha(Path(str(stem)+'.stdout')),'stderr_sha256':sha(Path(str(stem)+'.stderr'))})
 def changed(mode,name,path,transform):
  original=path.read_bytes()
  try:path.write_bytes(transform(original));run(mode,name,False)
  finally:path.write_bytes(original)
 for mode in [0,1,2]:
  run(mode,'valid-preflight',True)
  for spec,bank in zip(pins['banks'],[signed,mobius]):
   manifest=json.loads((testnet/spec['base']/'SOURCE_MANIFEST.json').read_text())
   for row in manifest['modules']:
    mod=row['module'];changed(mode,spec['label']+'-object-'+mod,bank/'objects'/(mod.replace('.','/')+'.olean'),lambda b:b+b'X')
    changed(mode,spec['label']+'-source-'+mod,bank/row['path'],lambda b:b+b'\n')
   rp=bank/'REPLAY_RESULT.json'
   changed(mode,spec['label']+'-duplicate-key',rp,lambda b:b.replace(b'{',b'{"status":"duplicate",',1))
   changed(mode,spec['label']+'-overflow-float',rp,lambda b:b.replace(b'{',b'{"probe":1e999,',1))
   changed(mode,spec['label']+'-nonfinite-float',rp,lambda b:b.replace(b'{',b'{"probe":NaN,',1))
   def altered(b,key,value):
    d=json.loads(b);d[key]=value;return json.dumps(d).encode()
   changed(mode,spec['label']+'-boolean-mode',rp,lambda b:altered(b,'python_optimization',False))
   def boolcode(b):
    d=json.loads(b);d['commands'][0]['returncode']=False;return json.dumps(d).encode()
   changed(mode,spec['label']+'-boolean-returncode',rp,boolcode)
   def missing(b):
    d=json.loads(b);d['commands'].pop();return json.dumps(d).encode()
   changed(mode,spec['label']+'-missing-child',rp,missing)
   log=bank/'logs'/f"{spec['audit_module']}.stdout";changed(mode,spec['label']+'-nonstandard-axiom',log,lambda b:b.replace(b'propext',b'Lean.ofReduceBool',1))
   extra=bank/'objects/UNRECORDED.olean'
   try:extra.write_bytes(b'not a proof object');run(mode,spec['label']+'-unrecorded-object',False)
   finally:extra.unlink()
  for row in pins['sources']:
   changed(mode,'canonical-'+row['module'],testnet/row['path'],lambda b:b+b'\n')
  changed(mode,'context-overflow-float',context,lambda b:b.replace(b'{',b'{"probe":1e999,',1))
  changed(mode,'context-duplicate-key',context,lambda b:b.replace(b'{',b'{"compiler":"duplicate",',1))
  run(mode,'unknown-option',False,extra=['--unknown'])
  run(mode,'abbreviated-option',False,extra=['--net',str(testnet)])
  run(mode,'full-canonical-build',True,check=False)
  print('PASS_MODE',mode,'cases',sum(x['mode']==mode for x in records),flush=True)
 # Every receipt must still identify its own unambiguous retained log preimage.
 for row in records:
  stem=out/'control-logs'/f"{row['mode']}-{row['case']}"
  need(sha(Path(str(stem)+'.stdout'))==row['stdout_sha256']and sha(Path(str(stem)+'.stderr'))==row['stderr_sha256'],'retained per-case log identity')
 # Fixtures are regenerable copies, never the only source/proof copy. Remove only
 # these checked experiment-owned copies after every completed gate passes.
 need(fixture.resolve().parent==out and fixture.is_dir()and not fixture.is_symlink(),'fixture cleanup boundary');actual_files={q.relative_to(fixture).as_posix()for q in fixture.rglob('*')if q.is_file()};need(actual_files==set(fixture_identity),'fixture cleanup complete identity inventory')
 for relative,identity in fixture_identity.items():
  q=fixture/relative;need(not q.is_symlink()and sha(q)==identity['sha256']and q.stat().st_size==identity['bytes'],'fixture cleanup original restored hash:'+relative)
 preview={'status':'VERIFIED_EXACT_REGENERABLE_FIXTURE_COPIES_BEFORE_DELETION','target':str(fixture),'files':fixture_identity,'accepted_original_banks_and_new_builds_excluded':True}
 preview_path=out/'CLEANUP_PREVIEW.json';preview_path.write_text(json.dumps(preview,indent=2)+'\n');size=sum(x['bytes']for x in fixture_identity.values());shutil.rmtree(fixture);need(not fixture.exists(),'fixture removal incomplete')
 result={'schema':'SIGNED_CANONICAL_NODES_ACTUAL_CLI_CONTROLS_V1','status':'PASS_ALL_MODES_ALL_ACTIVE_SOURCE_OBJECT_ROUTES_AND_NEGATIVE_CONTROLS','cases':len(records),'records':records,'elapsed_seconds':time.monotonic()-start,'controller_sha256':sha(__file__),'reproducer_sha256':sha(B/'reproduce_signed_nodes.py'),'pins_sha256':sha(B/'SIGNED_NODE_REPLAY_PINS.json'),'cleanup':{'verified_fixture_only':True,'bytes_removed':size,'preview_sha256':sha(preview_path),'exact_restored_files_hash_verified':True,'accepted_builds_and_logs_retained':True}}
 temp=out/'RESULT.json.pending';temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(out/'RESULT.json');print('PASS',len(records),'actualCLIcases',flush=True)
if __name__=='__main__':main()
