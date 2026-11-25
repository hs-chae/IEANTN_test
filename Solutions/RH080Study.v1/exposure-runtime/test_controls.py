#!/usr/bin/env python3
"""Actual additive runtime source-inspection CLI controls; never launch inference."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--repository',type=Path,required=True)
    ap.add_argument('--corpus',type=Path);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    R=a.repository.resolve(strict=True);E=R/'Solutions/RH080Study.v1/exposure-runtime'
    need(not a.run.exists(),'Fresh test storage required');a.run.mkdir(parents=True);out=a.run.resolve();rows=[]
    clone=out/'source-only/network';dst=clone/'Solutions/RH080Study.v1/exposure-runtime';shutil.copytree(E,dst,ignore=shutil.ignore_patterns('__pycache__'))
    def execute(name,command,good,marker):
        x=subprocess.run(list(map(str,command)),capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        (out/(name+'.stdout')).write_bytes(x.stdout);(out/(name+'.stderr')).write_bytes(x.stderr)
        need((x.returncode==0)==good,'Wrong disposition '+name);need(marker.encode() in (x.stdout if good else x.stderr),'Wrong source/CLI guard '+name)
        rows.append(dict(name=name,command=list(map(str,command)),returncode=x.returncode,expected_success=good,
                         stdout_sha256=sha(out/(name+'.stdout')),stderr_sha256=sha(out/(name+'.stderr')),intended_guard=marker))
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        prefix=[sys.executable]+flags;script=dst/'inspect_replay.py';receipt=out/(label+'-inspection.json')
        cmd=prefix+[script,'--repository',clone,'--output',receipt]+(['--corpus',a.corpus] if a.corpus else [])
        execute(label+'-inspection',cmd,True,'PASS_ADDITIVE_EXPOSURE_RUNTIME_SOURCE_AUDIT_NO_INFERENCE_NOT_TRIAL_READINESS')
        accepted=json.loads(receipt.read_text());need(accepted['ready_for_research_trials'] is False and accepted['model_calls']==0 and accepted['credentials_read'] is False,'Overstated source receipt')
        execute(label+'-stale-output',cmd,False,'Fresh output required')
        component=dst/'layout/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py';original=component.read_bytes();component.write_bytes(original+b'\n# changed generic source\n')
        target=out/(label+'-wrong-component.json')
        execute(label+'-changed-source',prefix+[script,'--repository',clone,'--output',target],False,'Reviewed runtime component differs:')
        need(not target.exists(),'Rejected source produced receipt');component.write_bytes(original)
        execute(label+'-lock-adapter-help',prefix+[dst/'check_lock.py','--help'],True,'--data-root')
    result=dict(status='PASS_12_ADDITIVE_RUNTIME_SOURCE_AND_CLI_CONTROLS_ALL_PYTHON_MODES_NO_INFERENCE',rows=rows,
                source_component_manifest_sha256=sha(E/'SOURCE_COMPONENTS.json'),controller_sha256=sha(Path(__file__)),
                model_calls=0,worker_launches=0,credentials_read=False,full_clean_root_trial_gate_tested=False,
                scope='Source/metadata availability and effective rejection controls; not runtime/fixture acceptance or a mathematical proof.')
    fd,name=tempfile.mkstemp(prefix='.receipt-',dir=out);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,out/'RESULT.json')
    finally:p.unlink()
    print(json.dumps(dict(status=result['status'],cases=len(rows))))


if __name__=='__main__':main()
