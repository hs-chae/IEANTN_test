#!/usr/bin/env python3
"""Bounded actual optimization-mode guards; the dense ray is not recomputed here."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    need(not os.path.lexists(a.run),'fresh controls');a.run.mkdir(parents=True);here=Path(__file__).resolve().parent;rows=[]
    def call(name,mode,script,flags,success):
        command=[sys.executable,*mode,'-B',str(here/script),*map(str,flags)];p=subprocess.run(command,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        (a.run/(name+'.stdout')).write_bytes(p.stdout);(a.run/(name+'.stderr')).write_bytes(p.stderr)
        need((p.returncode==0)==success,'Unexpected control status '+name)
        rows.append(dict(name=name,command=command,exit_code=p.returncode,expected_success=success,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest()))
    for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        replay=a.run/(label+'-slab')
        call(label+'-slab',mode,'reproduce.py',['--run',replay,'--slab-only'],True)
        numeric=replay/'Fap-numeric/RESULT.json';fft=here/'inputs/certify_integer.py'
        ray=here/'evidence/w4-global-chord-v2/RESULT.json'
        call(label+'-ray-application-receipt-replay',mode,'review_applicability.py',['--numerical-receipt',ray,'--fft-source',fft,'--run',a.run/(label+'-ray-app')],True)
        for field,badvalue in [('leading_margin','-1'),('status','REJECTED')]:
            d=json.loads(ray.read_text());d[field]=badvalue;bad=a.run/(label+'-'+field+'.json');bad.write_text(json.dumps(d));dest=a.run/(label+'-'+field)
            call(label+'-'+field,mode,'review_applicability.py',['--numerical-receipt',bad,'--fft-source',fft,'--run',dest],False)
            need(not(dest/'RESULT.json').exists(),'Rejected application emitted acceptance')
        for case,grid in [('bad-grid',1),('reuse',131072)]:
            dest=a.run/(label+'-'+case)
            if case=='reuse':dest.mkdir()
            call(label+'-'+case,mode,'review_global_chord.py',['--fft-source',fft,'--witness',here/'inputs/witness-ap.json','--run',dest,'--grid',grid],False)
            need(not(dest/'RESULT.json').exists(),'Rejected numeric emitted acceptance')
            profile=a.run/(label+'-profiles')
        call(label+'-profiles',mode,'review_profiles.py',['--run',profile],True)
        call(label+'-profiles-reuse',mode,'review_profiles.py',['--run',profile],False)
    result=dict(status='PASS_NORMAL_O_OO_EXPLICIT_REVIEW_CONTROLS',children=len(rows),fresh_slab_numeric_and_application_replays=3,
        ray_application_existing_receipt_replays=3,dense_ray_numerical_replays=0,fresh_profile_replays=3,negative_controls=15,controller_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        scope='Guard/portable slab controls; actual dense ray is independently recorded once plus a separate clean-folder full replay. No new Lean/PV claim.')
    tmp=a.run/'RESULT.json.tmp';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,a.run/'RESULT.json');tmp.unlink()
    print(json.dumps({k:result[k]for k in ['status','children','negative_controls']}))

if __name__=='__main__':main()
