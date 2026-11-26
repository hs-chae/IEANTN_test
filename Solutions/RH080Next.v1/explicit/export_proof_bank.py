#!/usr/bin/env python3
"""Export an existing real frozen-source replay to source-association format.

This is a receipt-format adapter, not another proof run or an acceptance claim.
Every source/object/log hash is checked against the original completed replay.
"""
import argparse, hashlib, json, os, shutil
from pathlib import Path

def need(v,m):
    if not v:
        raise ValueError(m)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(p,value):
    need(not p.exists(),'fresh receipt required')
    tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x') as f:
        json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:
        os.link(tmp,p)
    finally:
        tmp.unlink()

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False,description=__doc__)
    ap.add_argument('--replay',type=Path,required=True)
    ap.add_argument('--context',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args()
    result=a.replay/'RESULT.json';r=json.loads(result.read_text());c=json.loads(a.context.read_text())
    need(r['status']=='PASS','original replay did not pass')
    need(r['context_sha256']==sha(a.context),'dependency context differs')
    need(r['compiler_sha256']==sha(Path(c['compiler']))==c['compiler_sha256'],'compiler bytes differ')
    need(not a.out.exists(),'fresh export directory required')
    a.out.mkdir(parents=True)
    (a.out/'source').mkdir();(a.out/'objects').mkdir()
    repo=Path(__file__).resolve().parent.parents[2]
    plan=[]
    for row in r['source_manifest']:
        n=row['module'];relative=Path(n.replace('.','/'))
        origin=repo/row['source'];snapshot=a.replay/'frozen-source'/row['source']
        obj=a.replay/'objects'/relative.with_suffix('.olean')
        need(row['exit']==0 and not row['oom_observed'],'original source compile failed')
        need(sha(origin)==sha(snapshot)==row['source_sha256'],'current/snapshot source differs')
        need(sha(obj)==row['object_sha256'],'compiled object differs')
        for kind in ['stdout','stderr']:
            need(sha(a.replay/'logs'/(n+'.'+kind))==row[kind+'_sha256'],'original compiler log differs')
        need(sha(a.replay/'logs'/(n+'.time'))==row['usage_sha256'],'original resource receipt differs')
        target=a.out/'source'/relative.with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(snapshot.read_bytes())
        output=a.out/'objects'/relative.with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(obj,output)
        imports=[d for line in target.read_text().splitlines() if line.startswith('import ')
                 for d in line[7:].split('--',1)[0].split()]
        plan.append(dict(module=n,origin=str(origin),snapshot=str(target),source_sha256=sha(target),imports=imports))
        save(a.out/(n+'.COMPILED.json'),dict(status='FORMAT_EXPORT_OF_EXISTING_SUCCESSFUL_SOURCE_COLD_COMPILE',
            module=n,exitcode=0,source_sha256=sha(target),object_sha256=sha(output),
            original_command=row['command'],original_seconds=row['seconds'],peak_rss_kib=row['peak_rss_kib'],
            original_receipt=str(result),original_receipt_sha256=sha(result)))
    (a.out/'ORIGINAL_RESULT.json').write_bytes(result.read_bytes())
    save(a.out/'PLAN.json',dict(status='FORMAT_EXPORT_NOT_NEW_PROOF_OR_ACCEPTANCE',source_rows=plan,
        context_sha256=sha(a.context),original_receipt_sha256=sha(result),controller_sha256=sha(Path(__file__)),
        application_object_fallback=False))
    save(a.out/'RESULT.json',dict(status='EXPORTED_EXISTING_FROZEN_SOURCE_COLD_RECEIPTS_ONLY',modules=len(plan),
        new_proof_run=False,new_acceptance=False,original_receipt_sha256=sha(result)))
    print('EXPORTED',len(plan),'previously source-cold compiled modules; no new acceptance')

if __name__=='__main__':
    main()
