#!/usr/bin/env python3
"""Actual optimization-mode negative controls for final association/audit gates."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--phase',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(not os.path.lexists(a.out),'Fresh finalizer controls required');a.out.mkdir(parents=True)
    here=Path(__file__).resolve().parent;integration=here.parent
    actual=json.loads((a.phase/'PUBLIC_INTEGRATION_ADDENDUM_normal.json').read_text());need(len(actual['projects'])==12,'Actual current12 association required')
    fixtures={}
    for kind in ['bad-axiom','missing-root','bad-object']:
        root=a.out/('fixture-'+kind);(root/'core-final-v1').mkdir(parents=True);(root/'proof-audit-normal').mkdir()
        for n in ['RESULT.json','PLAN.json']:shutil.copy2(a.phase/'core-final-v1'/n,root/'core-final-v1'/n)
        p=json.loads((a.phase/'proof-audit-normal/RESULT.json').read_text())
        if kind=='bad-axiom':next(iter(p['rows'][0]['theorem_axioms'].values())).append('sorryAx');message='Nonstandard actual Solution proof axiom'
        elif kind=='missing-root':p['rows'][0]['theorem_axioms'].pop(next(iter(p['rows'][0]['theorem_axioms'])));message='Audited Solution root identities differ'
        else:p['rows'][0]['object_sha256']='0'*64;message='Audited Solution object changed'
        (root/'proof-audit-normal/RESULT.json').write_text(json.dumps(p))
        fixtures[kind]=(root,message)
    bad_lake=a.out/'fixture-bad-lake';bad_lake.mkdir();(bad_lake/'RESULT.json').write_text('{"status":"FAILED"}');(bad_lake/'PLAN.json').write_text('{}')
    rows=[]
    def call(name,command,message=None,success=False):
        p=subprocess.run(command,capture_output=True);(a.out/(name+'.stdout')).write_bytes(p.stdout);(a.out/(name+'.stderr')).write_bytes(p.stderr)
        need((p.returncode==0)==success,'Unexpected finalizer control status: '+name)
        if message:need(message in p.stderr.decode(),'Different guard rejected: '+name)
        rows.append(dict(name=name,command=command,exit_code=p.returncode,expected_success=success,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest()))
    for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        for kind,(phase,message)in fixtures.items():
            target=a.out/(label+'-'+kind+'.json')
            command=[sys.executable,*mode,str(integration/'finalize_integration.py'),'--phase',str(phase),'--lake-run',str(a.phase/'lake-all12-v1-OO'),'--controls',str(a.phase/'controls-final-v2-OO'),'--out',str(target)]
            call(label+'-'+kind,command,message);need(not target.exists(),'Rejected finalizer emitted acceptance')
        command=[sys.executable,*mode,str(integration/'finalize_integration.py'),'--phase',str(a.phase),'--lake-run',str(a.phase/'lake-all12-v1-OO'),'--controls',str(a.phase/'controls-final-v2-OO'),'--out',str(a.phase/'PUBLIC_INTEGRATION_ADDENDUM_normal.json')]
        call(label+'-existing-finalization',command,'Fresh integration addendum required')
        target=a.out/(label+'-bad-audit')
        call(label+'-bad-audit',[sys.executable,*mode,str(here/'audit_lake_solutions.py'),'--lake-run',str(bad_lake),'--out',str(target)],'Complete current actual Lake run required');need(not(target/'RESULT.json').exists(),'Rejected audit emitted acceptance')
        call(label+'-existing-gates',[sys.executable,*mode,str(here/'check_current.py'),'--phase',str(a.phase)],'Fresh phase gate outputs required')
        if label!='OO':
            phase=a.out/('actual-gates-'+label);phase.mkdir()
            call(label+'-actual-gates',[sys.executable,*mode,str(here/'check_current.py'),'--phase',str(phase)],success=True)
    result=dict(status='PASS_FINAL_INTEGRATION_ASSOCIATION_AUDIT_CURRENT_GATE_CONTROLS_ALL_MODES',cases=len(rows),negative_controls=18,
        actual_additional_current_graph_fingerprint_full49_checks=2,controller_sha256=sha(Path(__file__)),rows=rows,
        fixtures='Only intentionally unaccepted metadata/source fixtures; no application objects or positive proof receipts manufactured.')
    tmp=a.out/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,a.out/'RESULT.json');tmp.unlink()
    print(json.dumps({k:result[k]for k in ['status','cases','negative_controls']}))

if __name__=='__main__':main()
