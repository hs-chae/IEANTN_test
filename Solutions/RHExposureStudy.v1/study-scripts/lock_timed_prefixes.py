#!/usr/bin/env python3
"""Seal immutable actual technical snapshots at the prespecified common time horizons.

No worker feedback is sent. A coherent worker LOCK is separately checked; a draft
snapshot never becomes a completed portfolio merely by being copied or hashed.
"""
from pathlib import Path
import datetime,hashlib,json,shutil
R=Path(__file__).resolve().parents[1];D=Path('/data/ivy-rh-propagation-20261120')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for horizon in [900,1800,3600]:
 for arm in ['NL_RH','IEANTN_RH']:
  run=D/'runs'/('primary-'+arm+'-v1');idx=run/'CHECKPOINTS.json';target=R/'evaluator-private/checkpoints'/str(horizon)/arm
  if target.exists()or not idx.exists():continue
  records=json.loads(idx.read_text())['snapshots'];eligible=[row for row in records if row['elapsed_seconds']>=horizon]
  if not eligible:continue
  chosen=min(eligible,key=lambda row:row['elapsed_seconds']);source=Path(chosen['path']);receipt=json.loads((source/'SNAPSHOT.json').read_text());target.mkdir(parents=True);shutil.copytree(source/'files',target/'files');files=[]
  for row in receipt['files']:
   p=target/'files'/row['path']
   if sha(p)!=row['sha256']or p.stat().st_size!=row['bytes']:raise RuntimeError('sealed technical source differs')
   files.append({'path':row['path'],'sha256':row['sha256'],'bytes':row['bytes']})
  lock=target/'files/LOCK.json';consistent=False;reason='No worker LOCK in this actual snapshot; retain as draft evidence only'
  if lock.exists():
   try:
    data=json.loads(lock.read_text());seen=set()
    for row in data['files']:
     name=row['path']
     if name in seen or Path(name).name!=name:raise ValueError('invalid lockpath')
     seen.add(name)
     if sha(target/'files'/name)!=row['sha256']:raise ValueError('draft source changed relative to LOCK')
    consistent=True;reason='Every worker-listed source hash matches this immutable copied snapshot; mathematical claims still require review'
   except Exception as e:reason=str(e)
  result={'schema':'RH_TIMED_PREFIX_LOCK_V1','arm':arm,'prespecified_common_horizon_seconds':horizon,'actual_snapshot_start_elapsed_seconds':chosen['elapsed_seconds'],'actual_generated_tokens':chosen.get('generated_tokens'),'selection':'First available technical snapshot whose recorded start elapsed is at least the prespecified horizon; identical time-only rule, no mathematical outcome selection','mapping_detail_recorded_by':'/root during execution, before mathematical comparison; protocol fixed horizons before launch','source_snapshot':str(source),'source_snapshot_sha256':sha(source/'SNAPSHOT.json'),'technical_snapshot_quiesced':receipt.get('quiesced'),'atomic_cross_file_snapshot_claimed':False,'worker_lock_consistent':consistent,'consistency_note':reason,'immutable_bytes':files,'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mathematical_acceptance':'UNASSESSED','worker_feedback_sent':False}
  (target/'LOCKED_PREFIX.json').write_text(json.dumps(result,indent=2)+'\n');print(arm,horizon,round(chosen['elapsed_seconds'],3),len(files),'consistentlock',consistent)
