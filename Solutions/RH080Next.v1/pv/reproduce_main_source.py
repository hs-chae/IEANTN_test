#!/usr/bin/env python3
"""Portable clean-source entry point for the complete numerical C proof replay."""
import argparse,json,subprocess,sys
from pathlib import Path
from compile_verified_batch import atomic,need,sha
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',required=True,type=Path);ap.add_argument('--run',required=True,type=Path)
    ap.add_argument('--repository',type=Path,default=REPO)
    ap.add_argument('--inputs',type=Path,default=HERE/'evidence/MAIN_SOURCE_COLD_INPUTS.json')
    ap.add_argument('--scratch-root',required=True,type=Path)
    ap.add_argument('--workers',type=int,default=4);ap.add_argument('--worker-memory-gib',type=int,default=64)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repository=a.repository.resolve();run=a.run.resolve();inputs=json.loads(a.inputs.read_text())
    need(inputs['kind']=='SOURCE_IDENTITIES_ONLY_NO_APPLICATION_PROOF_CACHE','Wrong portable input kind')
    need(len(inputs['sources'])==inputs['modules'],'Portable source population differs')
    destination=run.with_name(run.name+'-inputs');need(not destination.exists() and not run.exists(),'Fresh experiment-owned destinations required')
    rows=[];names=set()
    for row in inputs['sources']:
        need(row['module'] not in names,'Duplicate portable compiler identity');names.add(row['module'])
        origin=(repository/row['path']).resolve();need(origin.is_relative_to(repository),'Source path escapes repository')
        need(origin.is_file() and sha(origin)==row['sha256'],'Portable pinned source differs '+row['module'])
        rows.append(dict(module=row['module'],source_origin=str(origin),source_sha256=row['sha256']))
    destination.mkdir(parents=True);inventory=destination/'SOURCE_INVENTORY.json'
    atomic(inventory,dict(full_dependency_cone=rows,portable_inputs_sha256=sha(a.inputs),portable_controller_sha256=sha(Path(__file__))))
    command=[sys.executable,str(HERE/'reproduce_main_source_cold.py'),'--context',str(a.context.resolve()),'--inventory',str(inventory),
      '--run',str(run),'--scratch-root',str(a.scratch_root.resolve()),'--workers',str(a.workers),'--worker-memory-gib',str(a.worker_memory_gib)]
    for root in inputs['roots']:command.extend(['--root',root])
    atomic(destination/'COMMAND.json',dict(command=command,prepared_sources=len(rows),application_object_cache=False,prepare_only=a.prepare_only))
    if a.prepare_only:print(json.dumps(dict(status='PASS_PORTABLE_SOURCE_PREPARATION_ONLY',modules=len(rows),inventory=str(inventory))));return
    subprocess.run(command,check=True)

if __name__=='__main__':main()
