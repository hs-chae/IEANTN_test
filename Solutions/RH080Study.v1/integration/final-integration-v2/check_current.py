#!/usr/bin/env python3
"""Run current graph/fingerprint/check gates; preserve the exact inherited49 failures."""
import argparse,hashlib,json,os,re,subprocess,time,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from register_lake import read_json


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def atomic(p,d):
    need(not p.exists(),'Fresh current-gate acceptance required');tmp=p.with_suffix('.pending');tmp.write_text(json.dumps(d,indent=2)+'\n');os.link(tmp,p);tmp.unlink()


def errors(text):
    rows=[];section=None
    for line in text.splitlines():
        if line.startswith('FAIL '):section=line[5:]
        elif line.startswith(('ok ','warn ','PASS ')):section=None
        elif section and line.startswith('  - '):rows.append([section,re.sub(r', not `[^`]+`$',', not `<CHECKOUT_REPOSITORY_IDENTITY>`',line[4:])])
    return sorted(rows)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--phase',type=Path,required=True);a=ap.parse_args()
    integration=Path(__file__).resolve().parent.parent;repository=integration.parents[2]
    need(a.phase.is_dir()and not(a.phase/'FINAL_STRUCTURAL_GATES.json').exists(),'Fresh phase gate outputs required')
    baseline_path=integration/'evidence/INHERITED_CHECK_COMPARISON.json';baseline=read_json(baseline_path)
    need(baseline['baseline_error_count']==49 and len(baseline['normalized_baseline_errors'])==49,'Exact inherited49 baseline required')
    rows=[]
    for name,command,expected in [('graph-current',['python3','scripts/ieantn.py','check-graph'],0),('fingerprints-current',['python3','scripts/ieantn.py','fingerprint','--check'],0),('check-current',['python3','scripts/ieantn.py','check'],1)]:
        need(not(a.phase/(name+'.stdout')).exists(),'Fresh structural log paths required');start=time.monotonic();p=subprocess.run(command,cwd=repository,capture_output=True)
        (a.phase/(name+'.stdout')).write_bytes(p.stdout);(a.phase/(name+'.stderr')).write_bytes(p.stderr)
        need(p.returncode==expected,'Unexpected actual structural-gate exit: '+name)
        rows.append(dict(name=name,command=command,returncode=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest()))
    actual=errors((a.phase/'check-current.stdout').read_text());need(actual==baseline['normalized_baseline_errors']and len(actual)==49,'New/different repository check errors')
    affected=[]
    for old in baseline['affected_receipts']:
        p=repository/old['path'];current=sha(p);need(current==old['current_sha256'],'Historical receipt bytes changed')
        ancestors={}
        for label,commit in baseline['baseline_commits'].items():
            proc=subprocess.run(['git','show',commit+':'+old['path']],cwd=repository,capture_output=True);need(proc.returncode==0,'Pinned ancestor receipt missing')
            value=hashlib.sha256(proc.stdout).hexdigest();need(value==current,'Historical ancestor receipt differs');ancestors[label]=value
        affected.append(dict(path=old['path'],current_sha256=current,identical_ancestor_blob_sha256=ancestors))
    comparison=dict(status='EXPECTED_INHERITED_FAILURE_EXACT49_NORMALIZED_ERRORS_AND_RECEIPT_BYTES_UNCHANGED',current_actual_check_returncode=1,
        baseline_stdout_sha256=baseline['baseline_stdout_sha256'],current_stdout_sha256=sha(a.phase/'check-current.stdout'),baseline_error_count=49,current_error_count=49,
        normalization='Only environment-dependent expected checkout repository identity after not is normalized; receiptpath/claimedrepository/category retained.',
        baseline_commits=baseline['baseline_commits'],normalized_baseline_errors=baseline['normalized_baseline_errors'],normalized_current_errors=actual,
        affected_receipts=affected,full_check_PASS_claimed=False,baseline_comparison_sha256=sha(baseline_path),ancestor_reads='Actual read-only git show; no Git mutations.')
    atomic(a.phase/'INHERITED_CHECK_COMPARISON.json',comparison)
    files={str(p.relative_to(repository)):sha(p)for p in sorted((repository/'IEANTN/Nodes').rglob('*'))if p.is_file()and p.name in ['formalization.yaml','Conclusions.lean','Challenge.lean','fingerprints.json']}
    gates=dict(status='PASS_CURRENT_GRAPH_FINGERPRINT_AND_EXACT_INHERITED49_COMPARISON',commands=rows,current_node_metadata_sha256=files,
        producer_sha256=sha(Path(__file__)),official_Comparator_approval=False)
    atomic(a.phase/'FINAL_STRUCTURAL_GATES.json',gates)
    print(json.dumps(dict(status=gates['status'],inherited_errors=len(actual),unchanged_receipts=len(affected))))

if __name__=='__main__':main()
