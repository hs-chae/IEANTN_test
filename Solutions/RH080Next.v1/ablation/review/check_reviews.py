#!/usr/bin/env python3
"""Strict independent exposure-review acceptance; effective under -O/-OO."""
import argparse,hashlib,json,os,re
from pathlib import Path
from audit_generator import audit_source,REQUIRED
D=Path('/data/ivy-rh080-next-20261125')
TRIALS=['fixed_width-B_named-r1','fixed_width-C_network-r0','prime_index-B_named-r1']
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(items):
    out={}
    for k,v in items:
        need(k not in out,'Duplicate JSON key');out[k]=v
    return out
def load(p):return json.loads(p.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def save(p,value):
    need(not p.exists(),'Fresh acceptance receipt required');tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x') as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--attempt',type=int,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    primary=load(D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json');need(len(primary['rows'])==16,'Wrong primary population')
    need({x['trial'] for x in primary['rows'] if x['discovery_admissible_for_evaluation']}==set(TRIALS),'Wrong admissible population')
    need(sum(x['stop_reason']=='GENERATED_OUTPUT_ADMISSION_CEILING' for x in primary['rows'])==13,'Primary ceiling population differs')
    rows=[]
    for trial in TRIALS:
        run=a.root/(trial+'-replay-v'+str(a.attempt));export=run/'submission';backend=load(run/'result.json');inputs=load(a.root/(run.name+'.INPUTS.json'))
        need(backend['mode']=='NOAUTH_FINAL_CONFIG_FIXTURE' and backend['stop_reason'] is None and backend.get('infrastructure_error') is None,'Incomplete no-auth review')
        need(backend['credentials_mounted_in_worker'] is False and backend['private_reasoning_collected'] is False,'Review boundary changed')
        lock=export/'LOCK.json';need(backend['artifact_export']['consistent'] is True and sha(lock)==backend['artifact_export']['lock_sha256'],'Export LOCK differs')
        files=load(lock)['files'];need(len(files)==len({x['path'] for x in files}) and 1<=len(files)<=15,'Invalid artifact population')
        for item in files:
            name=item['path'];p=export/name
            need(name==Path(name).name and p.is_file() and not p.is_symlink() and sha(p)==item['sha256'],'Exported payload differs')
        review=load(export/'REVIEW.json');need(review['status']=='COMPILED_AND_INDEPENDENTLY_AUDITED','Compilation/audit incomplete')
        need(review['external_model_inference_calls']==0,'Unexpected inference')
        for key in ['host_absent','auth_absent','controller_canary_absent','genericLean_available']:need(review['isolation'][key] is True,'Isolation probe failed')
        need(review['isolation']['pid_namespace']!=os.readlink('/proc/self/ns/pid'),'PID namespace not isolated')
        need(review['isolation']['net_namespace']!=os.readlink('/proc/self/ns/net'),'Network namespace not isolated')
        actual=D/'exposure-controller-v2/trials'/trial/'research-v1';original=load(actual/'result.json');summary=next(x for x in primary['rows'] if x['trial']==trial)
        need(sha(actual/'result.json')==summary['result_sha256']==inputs['primary_result_sha256'],'Original result changed')
        need(sha(actual/'submission/LOCK.json')==original['artifact_export']['lock_sha256']==inputs['primary_lock_sha256'],'Original LOCK changed')
        for item in load(actual/'submission/LOCK.json')['files']:need(sha(actual/'submission'/item['path'])==item['sha256'],'Original payload changed')
        records=review['records'];need(len(records)==2 and records[-1]['module']=='IndependentAudit','Wrong compiler routes')
        module=records[0]['module'];source=export/(module+'.lean')
        need(sha(source)==inputs['source_sha256']==review['source_sha256']==sha(actual/'submission'/(module+'.lean')),'Not exact submitted source')
        expected_audit=audit_source(trial,module).encode();need((export/'IndependentAudit.lean').read_bytes()==expected_audit,'Independent type/dependency audit changed')
        for record in records:
            n=record['module'];need(record['exitcode']==0 and record['object_sha256'] is not None,'Proof object missing')
            need(sha(export/(n+'.stdout'))==record['stdout_sha256'] and sha(export/(n+'.stderr'))==record['stderr_sha256'],'Compiler log identity changed')
            text=(export/(n+'.stdout')).read_text();err=(export/(n+'.stderr')).read_text()
            need(not re.search(r'\berror:|sorryAx|PANIC',text),'Unaccepted compiler diagnostics')
            need(err in ['', '/bin/bash: warning: setlocale: LC_ALL: cannot change locale (C.UTF-8)\n'],'Unexpected stderr')
        proof_rows=load(export/'THEOREMS.json');names=[x['declaration'] for x in proof_rows]
        need(len(names)>0 and len(names)==len(set(names)),'Collapsed/empty theorem population')
        for proof in proof_rows:
            need(set(proof['axioms'])<= {'propext','Classical.choice','Quot.sound'},'Nonstandard axiom')
            need(proof['type'] and proof['closure_count']>0,'Missing theorem type/proof closure')
        by_name={x['declaration']:x for x in proof_rows}
        for root,children in REQUIRED[trial].items():
            need(root in by_name,'Missing scored theorem '+root)
            for child in children:need(child in by_name[root]['application_closure'],'Missing actual proof dependency '+root+' -> '+child)
        audit_stdout=(export/'IndependentAudit.stdout').read_text()
        need(audit_stdout=='INDEPENDENT_EXPOSURE_AUDIT_PASS module='+module+' theorem_count='+str(len(proof_rows))+' standard3 expected-types actual-proof-dependencies\n','Unexpected audit diagnostics')
        rows.append(dict(trial=trial,status='PASS_UNMODIFIED_SUBMISSION_EXPECTED_TYPES_ALL_THEOREMS_STD3_REAL_DEPENDENCIES',source_sha256=sha(source),primary_lock_sha256=inputs['primary_lock_sha256'],primary_result_sha256=inputs['primary_result_sha256'],review_result_sha256=sha(export/'REVIEW.json'),backend_result_sha256=sha(run/'result.json'),theorem_table_sha256=sha(export/'THEOREMS.json'),theorem_count=len(proof_rows),scored_roots=list(REQUIRED[trial]),source= str(source),run=str(run),common_runtime_sha256=inputs['runtime_sha256'],supplemental_only=True))
    need(len({x['common_runtime_sha256'] for x in rows})==1,'Not one common final environment')
    result=dict(status='PASS_ALL3_ADMISSIBLE_IMMUTABLE_SUBMISSIONS_INDEPENDENTLY_REVIEWED',requested_population=16,mechanically_admissible_population=3,output_ceiling_stops_preserved=13,original28_edited=False,primary_results_edited=False,external_model_inference_calls=0,rows=rows,all_theorem_count=sum(x['theorem_count'] for x in rows),validator_sha256=sha(Path(__file__)),audit_generator_sha256=sha(Path(__file__).with_name('audit_generator.py')),source_first_PV_claimed=False,analytic_inputs_remain_explicit=True,scope='Submissions were produced within their original admitted trials; fresh compilation/audits are supplemental verification and do not change timed outcomes or cure13ceilingstops. No overall treatment superiority or optimality claim.')
    save(a.output,result);print(json.dumps(dict(status=result['status'],theorems=result['all_theorem_count'],receipt=str(a.output),sha256=sha(a.output))))
if __name__=='__main__':main()
