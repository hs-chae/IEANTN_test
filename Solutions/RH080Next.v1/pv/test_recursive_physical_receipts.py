#!/usr/bin/env python3
"""Bounded receipt-validator mutations; no native numerical process is rerun."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
RUNS=['recursive-physical-final-v1','recursive-physical-final-O-v1','recursive-physical-final-OO-v1']
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def write(p,data):
    if p.is_symlink():p.unlink()
    p.write_bytes(data)
def put(p,d):write(p,(json.dumps(d,indent=2)+"\n").encode())
def clone(source,target):
    target.mkdir()
    for n in RUNS:
        b=target/n;b.mkdir()
        for p in(source/n).iterdir():
            need(p.is_file(),'physical input must be flat artifact directory')
            if p.suffix=='.json':shutil.copyfile(p,b/p.name)
            else:(b/p.name).symlink_to(p)
def mutate_row(base,change):
    b=base/RUNS[0];r=load(b/'RESULT.json');x=load(b/'fap-O0.RECEIPT.json');change(b,x);put(b/'fap-O0.RECEIPT.json',x);r['runs'][0]=x;put(b/'RESULT.json',r)
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--runs-root',required=True,type=Path);ap.add_argument('--run',required=True,type=Path);a=ap.parse_args();need(not a.run.exists(),'fresh control directory required');a.run.mkdir();validator=HERE/'verify_recursive_physical_receipts.py'
    tests={
      'missing-route':'missing/duplicate/extra run route',
      'duplicate-route':'missing/duplicate/extra run route',
      'wrong-source':'preserved source/snapshot bytes',
      'disabled-ubsan':'compile flags/source/output association',
      'sentinel-output':'exact decimal-LF output',
      'partial-output':'exact decimal-LF output',
      'binary-mutation':'run source/executable identity',
      'stderr-exit0':'failed/diagnostic native execution',
      'invented-oom-zero':'unjustified OOM assertion',
      'rss-mismatch':'actual peak RSS association',
      'nonzero-exit':'failed/diagnostic native execution',
      'resource-exit-mismatch':'resource process completion',
      'controller-mutation':'executed controller identity',
      'duplicate-json-key':'duplicate JSON key'}
    manifests=[];directories=[]
    # The positive clone refers to the same24 retained observations, not24 new runs.
    positive=a.run/'positive-clone';clone(a.runs_root,positive);directories.append(positive)
    cmd=[sys.executable,str(validator),'--runs-root',str(positive),'--source-root',str(HERE),'--output',str(a.run/'POSITIVE_CLONE.json')]
    p=subprocess.run(cmd,capture_output=True,timeout=30);(a.run/'positive.stdout').write_bytes(p.stdout);(a.run/'positive.stderr').write_bytes(p.stderr);need(p.returncode==0,'unaltered fixture must pass before mutations')
    for name,reason in tests.items():
        base=a.run/name;clone(a.runs_root,base);directories.append(base);b=base/RUNS[0]
        if name in ['missing-route','duplicate-route']:
            d=load(b/'RESULT.json')
            if name=='missing-route':d['runs'].pop()
            else:d['runs'].append(d['runs'][0])
            put(b/'RESULT.json',d)
        elif name=='wrong-source':write(b/'fap_fft_recursive.c',(b/'fap_fft_recursive.c').read_bytes()+b'\n')
        elif name=='disabled-ubsan':
            # Mutate the actual UBSan route, not a selected non-sanitizer row.
            d=load(b/'RESULT.json');x=load(b/'fap-ubsan.RECEIPT.json');x['compile_command'].remove('-fsanitize=undefined');put(b/'fap-ubsan.RECEIPT.json',x);d['runs'][3]=x;put(b/'RESULT.json',d)
        elif name in ['sentinel-output','partial-output']:
            def output_change(b,x):
                raw=b'18446744073709551615\n'if name=='sentinel-output'else b'781796015790084776';write(b/'fap-O0.stdout',raw);x['stdout_sha256']=sha(b/'fap-O0.stdout');x['output']=raw.decode()
            mutate_row(base,output_change)
        elif name=='binary-mutation':write(b/'fap-O0.bin',(b/'fap-O0.bin').read_bytes()+b'X')
        elif name=='stderr-exit0':
            def stderr_change(b,x):write(b/'fap-O0.stderr',b'UBSAN diagnostic\n');x['stderr_sha256']=sha(b/'fap-O0.stderr')
            mutate_row(base,stderr_change)
        elif name=='invented-oom-zero':mutate_row(base,lambda b,x:x.update(oom_event='0'))
        elif name=='rss-mismatch':mutate_row(base,lambda b,x:x.update(peak_rss_kib=x['peak_rss_kib']+1))
        elif name=='nonzero-exit':mutate_row(base,lambda b,x:x.update(returncode=1))
        elif name=='resource-exit-mismatch':
            def time_change(b,x):write(b/'fap-O0.time',(b/'fap-O0.time').read_bytes().replace(b'Exit status: 0',b'Exit status: 1'));x['time_sha256']=sha(b/'fap-O0.time')
            mutate_row(base,time_change)
        elif name=='controller-mutation':write(b/'executed_controller.py',(b/'executed_controller.py').read_bytes()+b'\n')
        else:write(b/'RESULT.json',b'{"status":"PASS","status":"FAIL"}')
        for flags in [[],['-O'],['-OO']]:
            stem=name+('-'+flags[0][1:]if flags else '-normal');receipt=a.run/(stem+'.json');cmd=[sys.executable,*flags,str(validator),'--runs-root',str(base),'--source-root',str(HERE),'--output',str(receipt)]
            p=subprocess.run(cmd,capture_output=True,timeout=30);(a.run/(stem+'.stdout')).write_bytes(p.stdout);(a.run/(stem+'.stderr')).write_bytes(p.stderr)
            need(p.returncode!=0 and not receipt.exists()and reason in p.stderr.decode(),'wrong/missing rejection for '+stem)
            manifests.append(dict(case=name,flags=flags,expected_error=reason,exitcode=p.returncode,command=cmd))
    # Verified isolated fixtures are regenerable; retain scripts, logs and exact mutation recipes.
    preview=[str(x)for x in directories];put(a.run/'CLEANUP_PREVIEW.json',dict(owned_fixture_directories=preview,original_runs_untouched=True))
    for directory in directories:
        need(directory.parent==a.run and directory.is_dir()and not directory.is_symlink(),'cleanup ownership check');shutil.rmtree(directory);need(not directory.exists(),'fixture cleanup failed')
    record=dict(status='PASS_PHYSICAL_RECEIPT_VALIDATOR_ALL_MODES_AND_BOUNDED_MUTATIONS',positive_fixture_refers_to_existing_24=True,negative_cases=len(tests),negative_rejections=len(manifests),cases=manifests,validator_sha256=sha(validator),test_script_sha256=sha(Path(__file__)),regenerable_fixture_directories_removed=preview,original24_artifacts_modified=False,no_native_programs_rerun=True)
    put(a.run/'RESULT.json',record);print(json.dumps({k:record[k]for k in ['status','negative_cases','negative_rejections','original24_artifacts_modified','no_native_programs_rerun']}))
if __name__=='__main__':main()
