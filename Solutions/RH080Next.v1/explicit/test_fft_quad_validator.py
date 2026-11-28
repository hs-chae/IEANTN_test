#!/usr/bin/env python3
"""Actual CLI rejection tests on clearly synthetic negative receipt fixtures.
No fixture is a research run or a compiler/execution receipt. Accepted banks are
read-only. Temporary aliases/copies are removed after rejection is recorded.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,value):p.write_text(json.dumps(value,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',required=True,type=Path);ap.add_argument('--context',required=True,type=Path);ap.add_argument('--native',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args();need(not a.out.exists(),'fresh test output required');a.out.mkdir(parents=True);original=a.run.resolve(strict=True);validator=Path(__file__).with_name('verify_fft_quad_result.py');rows=[];began=time.monotonic()
    for mode in [[],['-O'],['-OO']]:
      for mutation in ['zero-exit-panic','failed-child','missing-import','changed-snapshot']:
        label=(mode[0][1:] if mode else 'normal')+'-'+mutation;fixture=a.out/('SYNTHETIC_NEGATIVE_ONLY-'+label);fixture.mkdir();(fixture/'source').mkdir();(fixture/'logs').mkdir();(fixture/'objects').symlink_to(original/'objects',target_is_directory=True);plan=json.loads((original/'PLAN.json').read_text());result=json.loads((original/'RESULT.json').read_text());plan['synthetic_negative_fixture_only']=True;result['synthetic_negative_fixture_only']=True
        for r in plan['source_rows']:
          n=r['module'];new=fixture/'source'/(n.replace('.','/')+'.lean');new.parent.mkdir(parents=True,exist_ok=True);new.write_bytes(Path(r['snapshot']).read_bytes());r['snapshot']=str(new);cr=json.loads((original/(n+'.COMPILED.json')).read_text());cr['synthetic_negative_fixture_only']=True;cr['command']=[s.replace(str(original),str(fixture)) for s in cr['command']]
          for ext in ['stdout','stderr','time']:(fixture/'logs'/(n+'.'+ext)).write_bytes((original/'logs'/(n+'.'+ext)).read_bytes())
          if n=='ExplicitFFTQuadAudit':
            if mutation=='zero-exit-panic':
              p=fixture/'logs'/(n+'.stdout');p.write_text(p.read_text()+'\nPANIC synthetic negative fixture\n');cr['stdout_sha256']=sha(p)
            if mutation=='failed-child':cr['exitcode']=17
          if n=='ExplicitFFTQuadSource' and mutation=='changed-snapshot':new.write_text(new.read_text()+'\n-- synthetic changed snapshot; no compilation claimed\n')
          write(fixture/(n+'.COMPILED.json'),cr)
          for i,item in enumerate(result['commands']):
            if item['module']==n:result['commands'][i]=cr
        if mutation=='missing-import':
          old=len(plan['accepted_dependencies']);plan['accepted_dependencies']=[r for r in plan['accepted_dependencies'] if r['module']!='GoldbachDirect.PureArgs'];need(len(plan['accepted_dependencies'])==old-1,'missing-import fixture target unavailable')
        write(fixture/'PLAN.json',plan);write(fixture/'RESULT.json',result)
        command=[sys.executable,*mode,str(validator),'--context',str(a.context),'--run',str(fixture),'--native',str(a.native),'--out',str(fixture/'MUST_NOT_ACCEPT')];r=subprocess.run(command,capture_output=True,text=True);wanted={'zero-exit-panic':'compiler diagnostics rejected ExplicitFFTQuadAudit','failed-child':'failed or inconsistent active child ExplicitFFTQuadAudit','missing-import':'missing active application import GoldbachDirect.PureArgs','changed-snapshot':'current/frozen source changed ExplicitFFTQuadSource'}[mutation];need(r.returncode!=0 and wanted in r.stderr and not (fixture/'MUST_NOT_ACCEPT/RESULT.json').exists(),'validator failed intended rejection: '+label+'\n'+r.stderr);rows.append(dict(optimization=mode,mutation=mutation,command=command,exitcode=r.returncode,expected_reason=wanted,stderr_sha256=hashlib.sha256(r.stderr.encode()).hexdigest()))
        # Verified-regenerable fixture only; remove no accepted source/object.
        need(fixture.parent==a.out and fixture.name.startswith('SYNTHETIC_NEGATIVE_ONLY-') and (fixture/'objects').is_symlink(),'cleanup scope rejected');shutil.rmtree(fixture)
    write(a.out/'RESULT.json',dict(status='PASS_QUAD_VALIDATOR_NEGATIVE_CLIS_NORMAL_O_OO',synthetic_fixtures_only=True,research_outcome=False,rows=rows,validator_sha256=sha(validator),script_sha256=sha(Path(__file__)),accepted_bank_untouched=str(original),temporary_fixtures_regenerated_and_removed=True,seconds=time.monotonic()-began));print('PASS twelve actual CLI rejection controls across normal/-O/-OO; accepted evidence untouched')
if __name__=='__main__':main()
