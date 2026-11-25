#!/usr/bin/env python3
"""Delete only hash-verified regenerable bulk from a completed study replay.

Keeps every accepted proof/object bank, original repository input and compact
receipt. Only six fixed subdirectories under this run's regeneration root can
be removed; the source/artifact inventory is checked before any mutation.
"""
import argparse,hashlib,json,os,shutil,tempfile
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):
    need(p.is_file() and not p.is_symlink(),'Expected regular generated file')
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()


def publish(p,value):
    need(not os.path.lexists(p),'Fresh cleanup receipt required')
    fd,name=tempfile.mkstemp(prefix='.cleanup-',dir=p.parent);q=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(q,p)
    finally:q.unlink()


def read(p):
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'Duplicate JSON key');result[key]=value
        return result
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,
                      parse_constant=lambda x:(_ for _ in ()).throw(ValueError('Non-finite JSON constant: '+x)))


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    run=a.run.resolve(strict=True);result=read(run/'RESULT.json')
    need(result['status'] in ['PASS_FULL_FROZEN_STUDY_MATHEMATICAL_REPRODUCTION','PASS_SELECTED_STUDY_REPRODUCTION','PASS_STUDY_REPLAY_CONTROLS_OMITTED'],'Completed wrapper required')
    need(result['lane'] in ['all','numerics'],'Completed numerical generation lane required')
    root=run/'regeneration';need(root.is_dir() and not root.is_symlink(),'Owned regeneration root missing')
    acceptance=read(root/'RESULT.json');manifest=root/'ARTIFACT_HASHES.json'
    need(sha(manifest)==acceptance['artifact_inventory_sha256'],'Generated inventory changed')
    inventory=read(manifest);rows={row['path']:row for row in inventory['files']}
    names=['cells-40/raw','cells-40/source','cells-28/raw','cells-28/source','shadow','C-frontend'];targets=[]
    for name in names:
        target=root/name;need(target.is_dir() and not target.is_symlink() and target.resolve().is_relative_to(root.resolve()),'Wrong fixed cleanup target')
        files=[]
        for p in target.rglob('*'):
            need(not p.is_symlink(),'Unexpected alias under generated target')
            if p.is_file():
                relative=p.relative_to(root).as_posix();need(relative in rows and sha(p)==rows[relative]['sha256'],'Generated artifact changed')
                files.append(relative)
        expected={name for name in rows if name.startswith(target.relative_to(root).as_posix()+'/')}
        need(set(files)==expected,'Cleanup target population differs from recorded artifact inventory')
        targets.append(dict(path=str(target),files=len(files),logical_bytes=sum(rows[f]['bytes'] for f in files)))
    plan=dict(status='PREVIEWED_HASH_VERIFIED_FIXED_GENERATABLE_SCRATCH_CLEANUP',run=str(run),targets=targets,
              result_sha256=sha(run/'RESULT.json'),artifact_inventory_sha256=sha(manifest),
              accepted_proof_banks_selected=False,original_repository_inputs_selected=False)
    publish(run/'CLEANUP_PLAN.json',plan)
    for row in targets:
        shutil.rmtree(row['path']);need(not Path(row['path']).exists(),'Cleanup incomplete')
    publish(run/'CLEANUP.json',dict(status='PASS_ONLY_VERIFIED_REGENERABLE_NUMERICAL_BULK_REMOVED',targets=targets,
         logical_bytes_removed=sum(row['logical_bytes'] for row in targets),plan_sha256=sha(run/'CLEANUP_PLAN.json'),
         retained=['Original repository inputs','All accepted application proof/source/object banks','Generated artifact SHA inventory','All cell generation/PLAN/RESULT/command/log receipts'],
         deterministic_regeneration='reproduce_study.py --lane numerics from the preserved exact input inventory'))
    print(json.dumps(dict(status='PASS_ONLY_VERIFIED_REGENERABLE_NUMERICAL_BULK_REMOVED',logical_bytes_removed=sum(x['logical_bytes'] for x in targets))))


if __name__=='__main__':main()
