#!/usr/bin/env python3
"""Supplemental exact-byte type exports for all13 censored original payloads.

All rows use the same richest ORIGINAL D runtime, offline/scripted execution,
zero research inference and unchanged primary inadmissibility. Types/Std3
exports are evidence for independent interpretation, not mathematical success.
The prior v1 scaffold and its executed packets are preserved separately.
"""
import argparse,asyncio,base64,hashlib,json,re
from pathlib import Path
from types import SimpleNamespace
import run_review as common
D=common.D
ROOT=D/'exposure-supplemental-replay-v2'
RUNTIME=D/'exposure-controller-v2/trials/fixed_width-D_source_PV-r1/runtime.json'
RUNTIME_SHA='23c22ffbd40173ce027d945da1be3141def8e58103b7622f2ffd7dc3999c436a'


def generic_audit(module):
    common.need(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',module) is not None,'Unsupported submitted module name')
    return 'import '+module+r'''
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option pp.fullNames true
open Lean Elab Command Meta
run_cmd do
  let env←getEnv
  let moduleName : Name:=`MODULE
  let constants:=env.constants.toList.filter (fun pair=>match env.getModuleIdxFor? pair.1 with
    | some i=>env.header.moduleNames[i]! == moduleName
    | none=>false)
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let mut rows : Array Json:=#[]
  let mut problems : Array Json:=#[]
  let mut theoremCount : Nat:=0
  for (name,info) in constants do
    let axioms←collectAxioms name
    let rendered←liftTermElabM <| Meta.ppExpr info.type
    let kind:=match info with
      | .thmInfo _=>"theorem" | .defnInfo _=>"definition" | .axiomInfo _=>"axiom"
      | .opaqueInfo _=>"opaque" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor"
      | .recInfo _=>"recursor" | .quotInfo _=>"quotient"
    let deps:=match info with
      | .thmInfo t=>t.value.getUsedConstants.toList.map toString
      | .defnInfo t=>t.value.getUsedConstants.toList.map toString
      | _=>[]
    if kind=="theorem" then theoremCount:=theoremCount+1
    let row:=Json.mkObj [("declaration",toJson name.toString),("kind",toJson kind),
      ("type",toJson rendered.pretty),("axioms",toJson (axioms.map toString)),("direct_dependencies",toJson deps)]
    rows:=rows.push row
    if kind=="axiom" || !(axioms.all allowed.contains) then problems:=problems.push row
  liftIO <| IO.FS.writeFile "/work/submission/EXPORT.MODULE.json" (Json.compress (Json.mkObj
    [("module",toJson moduleName.toString),("declarations",toJson rows),("problems",toJson problems),("theorems",toJson theoremCount)]))
  unless theoremCount>0 do throwError "No submitted theorem declarations"
  unless problems.isEmpty do throwError "Submitted axioms or nonstandard proof axioms: {problems.size}"
  logInfo m!"SUPPLEMENTAL_FULL_MODULE_TYPE_STD3_EXPORT_PASS module={moduleName} declarations={rows.size} theorems={theoremCount} CLAIM_INTERPRETATION_PENDING PRIMARY_INADMISSIBLE_UNCHANGED"
'''.replace('MODULE',module)


def worker_source(trial,sources,order,audits):
    data=dict(trial=trial,sources={name:dict(bytes=base64.b64encode(value).decode(),sha256=hashlib.sha256(value).hexdigest()) for name,value in sources.items()},order=order,audits={name:base64.b64encode(value.encode()).decode() for name,value in audits.items()})
    return 'DATA='+repr(data)+'\n'+r'''
import os,json,base64,hashlib,subprocess,time,re
from pathlib import Path
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
work=Path('/work');out=work/'submission';out.mkdir();(work/'objects').mkdir(exist_ok=True)
probe=dict(host_absent=not Path('/ryu/hyunsik/playground/independence/codex/ivy/memory').exists(),auth_absent=not Path('/home/worker/.codex/auth.json').exists(),controller_canary_absent=not Path('host-only-canary.txt').exists(),pid_namespace=os.readlink('/proc/self/ns/pid'),net_namespace=os.readlink('/proc/self/ns/net'),genericLean_available=Path('/opt/lean/bin/lean').is_file())
need(all(probe[k] for k in ['host_absent','auth_absent','controller_canary_absent','genericLean_available']),'Isolation probe failed')
for name,item in DATA['sources'].items():
    path=work/(name+'.lean');path.write_bytes(base64.b64decode(item['bytes'],validate=True));need(sha(path)==item['sha256'],'Exact locked source bytes differ');(out/path.name).write_bytes(path.read_bytes())
records=[];compiled=[]
def compile(name,path,stage):
    obj=work/'objects'/(name+'.olean');command=['/bin/lean','-j2','--root=/work','-o',str(obj),str(path)];start=time.monotonic()
    try:
        p=subprocess.run(command,capture_output=True,text=True,timeout=540);stdout=p.stdout;stderr=p.stderr;code=p.returncode
    except subprocess.TimeoutExpired as e:
        stdout=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else e.stdout or '';stderr=(e.stderr or b'').decode() if isinstance(e.stderr,bytes) else e.stderr or '';code=124
    (out/(name+'.stdout')).write_text(stdout);(out/(name+'.stderr')).write_text(stderr)
    diagnostic=bool(re.search(r'PANIC|sorryAx|(?m:^|:)\s*error(?::|\()',stdout+stderr))
    accepted=code==0 and obj.is_file() and not diagnostic
    row=dict(module=name,stage=stage,source_sha256=sha(path),command=command,exitcode=code,seconds=time.monotonic()-start,stdout_sha256=sha(out/(name+'.stdout')),stderr_sha256=sha(out/(name+'.stderr')),object_sha256=sha(obj) if obj.exists() else None,strict_compile_accepted=accepted)
    records.append(row);return accepted
for module in DATA['order']:
    if compile(module,work/(module+'.lean'),'EXACT_SUBMITTED_SOURCE'):
        compiled.append(module)
        name='IndependentAudit_'+module;path=work/(name+'.lean');path.write_bytes(base64.b64decode(DATA['audits'][module],validate=True));(out/path.name).write_bytes(path.read_bytes());compile(name,path,'FULL_MODULE_TYPES_AXIOMS')
complete=len(compiled)==len(DATA['order']) and len(records)==2*len(DATA['order']) and all(row['strict_compile_accepted'] for row in records)
result=dict(status='ALL_LOCKED_LEAN_MODULES_COMPILED_AND_STD3_EXPORTED' if complete else 'SOURCE_COMPILE_OR_FULL_MODULE_AXIOM_EXPORT_FAILED',trial=DATA['trial'],source_modules=DATA['order'],source_sha256={name:item['sha256'] for name,item in DATA['sources'].items()},isolation=probe,records=records,lean_version=subprocess.check_output(['/bin/lean','--version'],text=True).strip(),lean_path=os.environ.get('LEAN_PATH'),external_model_inference_calls=0,primary_eligible=False,scope='SUPPLEMENTAL_FULL_MODULE_TYPES_NOT_EXPECTED_TYPE_OR_MATH_NOVELTY_OR_PRIMARY_SUCCESS')
(out/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');files=[dict(path=p.name,sha256=sha(p)) for p in sorted(out.iterdir()) if p.is_file()];(out/'LOCK.json').write_text(json.dumps(dict(files=files),indent=2)+'\n');print(json.dumps(dict(trial=DATA['trial'],status=result['status'],modules=DATA['order'],probe=probe)),flush=True)
'''


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--trial',required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    common.need(args.out.resolve().is_relative_to(ROOT) and not args.out.exists(),'Fresh experiment-owned supplemental-v2 directory required');args.out.parent.mkdir(parents=True,exist_ok=True)
    primary=D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json';summary=common.load(primary);rows=summary['rows'];common.need(len(rows)==len({r['trial'] for r in rows})==16,'Locked population changed')
    censored={r['trial'] for r in rows if not r['discovery_admissible_for_evaluation']};common.need(len(censored)==13 and args.trial in censored,'Only exact13 censored payloads use this route')
    selected=next(r for r in rows if r['trial']==args.trial);common.need(selected['stop_reason']=='GENERATED_OUTPUT_ADMISSION_CEILING','Original censoring classification changed')
    trial=D/'exposure-controller-v2/trials'/args.trial/'research-v1';result=common.load(trial/'result.json');common.need(common.sha(trial/'result.json')==selected['result_sha256'],'Primary result changed')
    lock=trial/'submission/LOCK.json'
    for export in [result['artifact_export'],selected['artifact_export']]:
        if export.get('lock_sha256') is not None:common.need(common.sha(lock)==export['lock_sha256'],'Original declared export LOCK changed')
    preflight=common.load(D/'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json');locked=next(r for r in preflight['rows'] if r['trial']==args.trial);common.need(common.sha(lock)==locked['lock_sha256'],'Preflight fixed lock differs')
    recovery_path=D/'exposure-supplemental-recovery-v1/RESULT.json';recovery=common.load(recovery_path)
    recovered=next(r for r in recovery['rows'] if r['trial']==args.trial)
    common.need(recovered['lock_sha256']==common.sha(lock),'Recovered original LOCK identity differs')
    source_root=Path(recovered['recovered_directory']);common.need((source_root/'LOCK.json').read_bytes()==lock.read_bytes(),'Recovered original LOCK bytes differ')
    files=common.load(lock)['files'];common.need(len(files)==len({r['path'] for r in files}),'Duplicate payload identity');missing=[];sources={};original_hashes={}
    for row in files:
        original=trial/'submission'/row['path'];common.need(original.name==row['path'] and not original.is_symlink(),'Invalid original payload identity')
        original_hashes[row['path']]=common.sha(original) if original.is_file() else None
        p=source_root/row['path'];common.need(p.is_file() and not p.is_symlink() and common.sha(p)==row['sha256'],'Recovered exact locked payload differs')
        if not original.is_file():missing.append(row)
        if p.name.endswith('.lean'):sources[p.stem]=p.read_bytes()
    common.need(sorted(m+'.lean' for m in sources)==sorted(locked['lean_files']),'All original Lean files must be covered')
    dependencies={m:[n for line in s.decode().splitlines() if line.startswith('import ') for n in line[7:].split('--',1)[0].split() if n in sources] for m,s in sources.items()};order=[];active=set();seen=set()
    def visit(m):
        if m in seen:return
        common.need(m not in active,'Original submitted import cycle');active.add(m)
        for n in dependencies[m]:visit(n)
        active.remove(m);seen.add(m);order.append(m)
    for m in sources:visit(m)
    audits={m:generic_audit(m) for m in order};script=worker_source(args.trial,sources,order,audits);packet=args.out.parent/(args.out.name+'-packet');common.need(not packet.exists(),'Fresh packet required');packet.mkdir()
    (packet/'TASK.md').write_text('Scripted supplemental full-module compiler/type/Std3 export only. Zero inference. All13 primary inadmissible classifications remain unchanged.\n');(packet/'WORKER_SCRIPT.py').write_text(script)
    for m,audit in audits.items():(packet/('IndependentAudit_'+m+'.lean')).write_text(audit)
    common.need(common.sha(RUNTIME)==RUNTIME_SHA,'Exact richest original common runtime changed');runtime=common.load(RUNTIME);adapter=common.module_at('supplement_pinned_adapter',common.S/'ablation/native_trial.py');common.need(common.sha(common.BACKEND)==common.BACKEND_SHA,'Pinned offline executor changed')
    for mount in runtime['mounts']:adapter.check_tree(Path(mount['source']),mount['manifest'])
    common.need(runtime['external_network'] is False and runtime['host_tools'] is False,'Original offline boundary changed')
    config=SimpleNamespace(out=args.out,packet=packet,model='gpt-6.2-sol',effort='high',fixture=True,wall=1200,output=18000,operations=180,responses=96,memory_gib=64,scratch_gib=12,cpus=4,per_response_max_output_tokens=None,phase='CENSORED_SUPPLEMENTAL_ALL_MODULE_EXPORT_NOT_PRIMARY',fixture_hook_fault=False,fixture_artifact_name='REVIEW.json',fixture_boundary_steps=1,fixture_draft_at=1,fixture_budget_prefix=False,paired_task_seed=0,compiler=False,python_only=False,environment='',python_optimization=0)
    core=adapter.import_backend();core.configure_runtime(runtime,config);core.Fixture=common.scripted_handler(core.Fixture,script);core.make_prompt=lambda p:(p/'TASK.md').read_text()
    pins=dict(trial=args.trial,primary_summary_sha256=common.sha(primary),primary_result_sha256=common.sha(trial/'result.json'),primary_lock_sha256=common.sha(lock),source_sha256={m:hashlib.sha256(s).hexdigest() for m,s in sources.items()},module_order=order,missing_original_nonLean_artifacts=missing,common_runtime=str(RUNTIME),common_runtime_sha256=RUNTIME_SHA,worker_script_sha256=common.sha(packet/'WORKER_SCRIPT.py'),backend_sha256=common.sha(common.BACKEND),controller_sha256=common.sha(Path(__file__)),recovery_result_sha256=common.sha(recovery_path),recovered_exact_locked_directory=str(source_root),original_submission_hashes=original_hashes,external_model_inference_calls=0,primary_eligible=False,scope='SUPPLEMENTAL_FULL_MODULE_TYPE_EXPORT_NOT_MATH_SUCCESS_OR_PRIMARY_RECLASSIFICATION')
    common.save(args.out.parent/(args.out.name+'.INPUTS.json'),pins);(packet/'run_supplemental.executed.py').write_bytes(Path(__file__).read_bytes());asyncio.run(core.main(config))
    common.need(common.sha(primary)==pins['primary_summary_sha256'] and common.sha(lock)==pins['primary_lock_sha256'] and common.sha(trial/'result.json')==pins['primary_result_sha256'],'Original evidence changed during replay')
    for row in files:
        original=trial/'submission'/row['path'];actual=common.sha(original) if original.is_file() else None
        common.need(actual==original_hashes[row['path']],'Original exported bytes changed during supplemental replay')
        common.need(common.sha(source_root/row['path'])==row['sha256'],'Exact recovered locked bytes changed')
    print('SUPPLEMENTAL_REPLAY_FINISHED',args.trial,flush=True)

if __name__=='__main__':main()
