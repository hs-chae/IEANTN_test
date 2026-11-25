#!/usr/bin/env python3
"""Actual fixed-directory cleanup CLI controls in all Python modes.

All artifacts here are synthetic disposable fixtures, never mathematical proof
acceptances. Checks preserve unselected proof/input sentinels and reject altered
hashes/ambiguous JSON before deleting any selected directory.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def fixture(p):
    p.mkdir();r=p/'regeneration';r.mkdir();rows=[]
    for name in ['cells-40/raw','cells-40/source','cells-28/raw','cells-28/source','shadow','C-frontend']:
        q=r/name;q.mkdir(parents=True);f=q/'data';f.write_bytes(b'GENERATABLE_TEST_FIXTURE_NO_MATH\n');rows.append(dict(path=f.relative_to(r).as_posix(),sha256=sha(f),bytes=f.stat().st_size))
    m=r/'ARTIFACT_HASHES.json';m.write_text(json.dumps(dict(files=rows)))
    (r/'RESULT.json').write_text(json.dumps(dict(artifact_inventory_sha256=sha(m))))
    (p/'RESULT.json').write_text(json.dumps(dict(status='PASS_SELECTED_STUDY_REPRODUCTION',lane='numerics')))
    (p/'objects').mkdir();(p/'objects/accepted-proof-sentinel').write_text('PRESERVE')
    (p/'original-input-sentinel').write_text('PRESERVE')
    return p


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    need(not a.run.exists(),'Fresh synthetic controls required');a.run.mkdir(parents=True);root=a.run.resolve();script=Path(__file__).with_name('cleanup_reproduction_scratch.py');rows=[]
    def call(label,flags,p,good,marker):
        cmd=[sys.executable]+flags+[str(script),'--run',str(p)];x=subprocess.run(cmd,capture_output=True)
        (root/(label+'.stdout')).write_bytes(x.stdout);(root/(label+'.stderr')).write_bytes(x.stderr)
        need((x.returncode==0)==good,'Wrong cleanup disposition '+label);need(marker.encode() in (x.stdout if good else x.stderr),'Wrong actual cleanup guard '+label)
        need((p/'objects/accepted-proof-sentinel').read_text()=='PRESERVE' and (p/'original-input-sentinel').read_text()=='PRESERVE','Unselected input/proof sentinel changed')
        rows.append(dict(label=label,command=cmd,returncode=x.returncode,expected_success=good,intended_guard=marker,
                         stdout_sha256=sha(root/(label+'.stdout')),stderr_sha256=sha(root/(label+'.stderr'))))
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        p=fixture(root/(label+'-positive'));call(label+'-positive',flags,p,True,'PASS_ONLY_VERIFIED_REGENERABLE_NUMERICAL_BULK_REMOVED')
        need(not(p/'regeneration/shadow').exists(),'Actual cleanup did not remove selected fixture')
        p=fixture(root/(label+'-bad-hash'));m=p/'regeneration/ARTIFACT_HASHES.json';x=json.loads(m.read_text());x['files'][0]['sha256']='0'*64;m.write_text(json.dumps(x));(p/'regeneration/RESULT.json').write_text(json.dumps(dict(artifact_inventory_sha256=sha(m))))
        call(label+'-bad-hash',flags,p,False,'Generated artifact changed');need((p/'regeneration/shadow/data').is_file(),'Rejected hash control deleted data')
        p=fixture(root/(label+'-duplicate'));(p/'RESULT.json').write_text('{"status":"x","status":"y"}')
        call(label+'-duplicate',flags,p,False,'Duplicate JSON key');need((p/'regeneration/shadow/data').is_file(),'Rejected duplicate control deleted data')
    receipt=dict(status='PASS_9_ACTUAL_CLEANUP_CLI_CONTROLS_ALL_PYTHON_MODES_SYNTHETIC_ONLY',rows=rows,script_sha256=sha(script),controller_sha256=sha(Path(__file__)),real_research_artifacts_used=False)
    fd,name=tempfile.mkstemp(prefix='.receipt-',dir=root);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(receipt,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,root/'RESULT.json')
    finally:p.unlink()
    print(json.dumps(dict(status=receipt['status'],cases=len(rows))))


if __name__=='__main__':main()
