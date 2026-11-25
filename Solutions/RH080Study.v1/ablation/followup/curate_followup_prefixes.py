#!/usr/bin/env python3
"""Copy the final admissible prefix of each completed trial, preserving bytes.

All eligible prefixes remain in the provenance readback/original private bank.
This public artifact selection is explicit and is not an audit inclusion rule.
"""
import argparse,hashlib,json,os,shutil
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(path):
    need(path.is_file() and not path.is_symlink(),'Regular artifact required')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--audit',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--source-root',type=Path)
    a=p.parse_args();need(not os.path.lexists(a.out),'Fresh curated output required')
    audit=json.loads(a.audit.read_text());need(audit['count']==8 and audit['valid_prefix_trials']==8,'All eight admitted trials required')
    plans=[]
    for trial in audit['trials']:
        selected=trial['timely_prefixes'][-1];name=Path(selected['path']).name
        source=a.source_root/trial['id']/name if a.source_root else Path(selected['path'])
        need(sha(source/'RECEIPT.json')==selected['receipt_sha256'],'Original prefix receipt differs')
        need(sha(source/'LOCK.json')==selected['lock_sha256'],'Original prefix LOCK differs')
        for row in selected['files']:
            need(row['file']==Path(row['file']).name and sha(source/row['file'])==row['sha256'],'Original mathematical artifact differs')
        plans.append((trial,selected,source,name))
    a.out.mkdir(parents=True);rows=[]
    for trial,selected,source,name in plans:
        destination=a.out/trial['id']/name;destination.mkdir(parents=True)
        copied=[]
        for filename in [r['file']for r in selected['files']]+['LOCK.json','RECEIPT.json']:
            target=destination/filename;shutil.copyfile(source/filename,target)
            need(sha(target)==sha(source/filename),'Curated copy differs')
            copied.append(dict(path=str(target.relative_to(a.out)),sha256=sha(target),bytes=target.stat().st_size))
        rows.append(dict(trial=trial['id'],prefix=name,files=copied,source_prefix_receipt_sha256=selected['receipt_sha256']))
    result=dict(status='PASS_BYTE_IDENTICAL_CURATED_FINAL_ADMISSIBLE_PREFIXES_ALL_EIGHT',trials=rows,
        source_audit_sha256=sha(a.audit),controller_sha256=sha(Path(__file__)),
        artifact_selection='Final admitted consistent prefix per trial. All earlier eligible-prefix metadata and originals are preserved; selection does not redefine the audited eight-trial universe.',
        raw_model_or_executor_trajectories_included=False,full_papers_or_credentials_included=False)
    (a.out/'CURATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],trials=8,files=sum(len(r['files'])for r in rows))))


if __name__=='__main__':main()
