#!/usr/bin/env python3
"""Actual bounded controller CLI controls: preparation only, never a proof PASS."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
Q=Path(__file__).resolve().parent;OUT=Q/'compact-controller-cli-controls-v2'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    need(not OUT.exists(),'Fresh controls required');OUT.mkdir();controller=Q/'compile_compact_final_v2.py';records=[]
    modified=OUT/'modified-assembly';shutil.copytree(Q/'s13-compact-v2',modified);j=json.loads((modified/'ASSEMBLY.json').read_text());j['same_public_FQ_names_and_type_headers']=False;(modified/'ASSEMBLY.json').write_text(json.dumps(j)+'\n')
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        positive=OUT/f'prepare-{mode}'
        def run(label,assembly=None,physical=64,target=None,positive_case=False,extra=None):
            target=target or OUT/f'{label}-{mode}';assembly=assembly or Q/'s13-compact-v2';cmd=[sys.executable,*flags,str(controller),'--assembly',str(assembly),'--run',str(target),'--physical-gib',str(physical),'--prepare-only',*(extra or[])];r=subprocess.run(cmd,capture_output=True,text=True)
            need((r.returncode==0)==positive_case,'Unexpected controller CLI status '+label)
            if positive_case:
                need((target/'PLAN.json').is_file()and not(target/'RESULT.json').exists(),'Preparation falsely published acceptance')
                need(len(json.loads((target/'PLAN.json').read_text())['inherited_closed_leaves'])==118,'Wrong prepared source closure')
            else:need(not(target/'RESULT.json').exists(),'Rejected controller published acceptance')
            records.append(dict(mode=mode,label=label,command=cmd,returncode=r.returncode,positive_preparation_only=positive_case,stdout=r.stdout,stderr=r.stderr))
        run('positive',target=positive,positive_case=True)
        run('stale-run',target=positive)
        run('wrong-stage-physical',physical=300)
        run('owned64-rejects-N24-300-policy',assembly=Q/'s24-compact-v2',physical=300)
        run('modified-assembly',assembly=modified)
        run('unknown-option',extra=['--unknown-acceptance-flag'])
    value=dict(status='PASS_ACTUAL_COMPACT_CONTROLLER_CLI_ALL_MODES_PREPARATION_ONLY',controller_sha256=sha(controller),control_source_sha256=sha(Path(__file__)),positive_preparations=3,negative_controls=15,mathematical_children_launched=0,records=records)
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=OUT)
    try:
        with os.fdopen(fd,'w')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,OUT/'RESULT.json')
    finally:Path(tmp).unlink()
    print(value['status'],sha(OUT/'RESULT.json'))
if __name__=='__main__':main()
