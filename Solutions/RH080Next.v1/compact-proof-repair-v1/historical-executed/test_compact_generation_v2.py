#!/usr/bin/env python3
"""Actual CLI source-generation positives and fail-closed mutation controls."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
Q=Path(__file__).resolve().parent;D=Q.parent;OUT=Q/'compact-generation-controls-v3'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    need(not OUT.exists(),'Fresh control directory required');OUT.mkdir();gen=Q/'generate_compact_final_v2.py';helpers=Q/'compact-helpers-v1';fixtures=OUT/'fixtures';fixtures.mkdir();records=[]
    banks={13:D/'w4-fresh-unlimited-actual-controls-v1/fresh-0',24:D/'w4-dag24-kernel-nested-resume-v4-thp0-v1'}
    for stage,bank in banks.items():
        source=bank/'sources'/f'W4D{stage}ClaimAudit.lean';s=source.read_text();old='13560177159173855'if stage==13 else'7813568381279800';need(old in s,'Actual audit numeral missing');(fixtures/f'W4D{stage}AuditMutated.lean').write_text(s.replace(old,str(int(old)+1)))
    bad_final=fixtures/'FinalMutated.lean';bad_final.write_text((banks[24]/'sources/W4D24Final.lean').read_text()+'\n-- changed final identity\n')
    bad_helpers=fixtures/'helpers';shutil.copytree(helpers,bad_helpers);(bad_helpers/'NormSymbolic.lean').write_text((bad_helpers/'NormSymbolic.lean').read_text()+'\n-- changed helper identity\n')
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        for stage in[13,24]:
            bank=banks[stage];final=bank/'sources'/f'W4D{stage}Final.lean';audit=bank/'sources'/f'W4D{stage}ClaimAudit.lean';positive=OUT/f'positive-{stage}-{mode}'
            def run(label,fp=final,ap=audit,hp=helpers,st=stage,target=None,expected=1):
                target=target or OUT/f'{label}-{stage}-{mode}';cmd=[sys.executable,*flags,str(gen),'--stage',str(st),'--original-final',str(fp),'--original-audit',str(ap),'--helper-dir',str(hp),'--out',str(target)];r=subprocess.run(cmd,capture_output=True,text=True);passed=r.returncode==0
                need(passed==(expected==0),'Unexpected actual control result '+label)
                if expected!=0:need(not (target/'ASSEMBLY.json').exists() or label=='stale-out','Rejected source generator published acceptance manifest')
                record=dict(mode=mode,stage=stage,label=label,command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr,expected=expected)
                if passed:record['assembly_sha256']=sha(target/'ASSEMBLY.json')
                records.append(record)
            run('positive',target=positive,expected=0)
            run('same-count-mutated-audit',ap=fixtures/f'W4D{stage}AuditMutated.lean')
            run('modified-final',fp=bad_final)
            run('modified-helper',hp=bad_helpers)
            run('stage-mismatch',st=24 if stage==13 else 13)
            old=sha(positive/'ASSEMBLY.json');run('stale-out',target=positive);need(sha(positive/'ASSEMBLY.json')==old,'Stale output mutated')
    for stage in[13,24]:
        hashes={r['assembly_sha256']for r in records if r['label']=='positive'and r['stage']==stage};need(len(hashes)==1,'Generation differs under Python optimization')
    result=dict(status='PASS_ACTUAL_COMPACT_GENERATOR_ALL_PYTHON_MODES',generator_sha256=sha(gen),controls_sha256=sha(Path(__file__)),positive_controls=sum(r['expected']==0 for r in records),negative_controls=sum(r['expected']!=0 for r in records),records=records,original_files_unmodified=True)
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=OUT)
    try:
        with os.fdopen(fd,'w')as f:json.dump(result,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,OUT/'RESULT.json')
    finally:Path(tmp).unlink()
    print(result['status'],result['positive_controls'],result['negative_controls'],sha(OUT/'RESULT.json'))
if __name__=='__main__':main()
