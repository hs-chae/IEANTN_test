#!/usr/bin/env python3
"""Portable clean-source entry point for the complete numerical C proof replay."""
import argparse,json,subprocess,sys,re
from pathlib import Path
from compile_verified_batch import atomic,need,sha
from final_fap_source_data_v2 import portable_data,relative,read_json
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',required=True,type=Path);ap.add_argument('--run',required=True,type=Path)
    ap.add_argument('--repository',type=Path,default=REPO)
    ap.add_argument('--inputs',type=Path,default=HERE/'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json')
    ap.add_argument('--scratch-root',required=True,type=Path)
    ap.add_argument('--workers',type=int,default=4);ap.add_argument('--worker-memory-gib',type=int,default=64)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repository=a.repository.resolve();run=a.run.resolve();inputs=read_json(a.inputs)
    need(inputs['kind']=='SOURCE_AND_LITERAL_DATA_IDENTITIES_NO_APPLICATION_PROOF_CACHE' and inputs['schema_version']==2,'Wrong portable input kind')
    need(type(inputs['modules']) is int and inputs['modules']==681 and len(inputs['sources'])==inputs['modules'],'Portable source population differs')
    destination=run.with_name(run.name+'-inputs');need(not destination.exists() and not run.exists(),'Fresh experiment-owned destinations required')
    rows=[];names=set()
    for row in inputs['sources']:
        need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',row['module']) is not None,'Invalid Lean module identity')
        relative(row['path'],'Lean source input path')
        need(row['module'] not in names,'Duplicate portable compiler identity');names.add(row['module'])
        origin=(repository/row['path']).resolve();need(origin.is_relative_to(repository),'Source path escapes repository')
        need(origin.is_file() and sha(origin)==row['sha256'],'Portable pinned source differs '+row['module'])
        rows.append(dict(module=row['module'],source_origin=str(origin),source_sha256=row['sha256']))
    need(type(inputs['data_file_count']) is int and inputs['data_file_count']==34 and type(inputs['literal_data_bytes']) is int and inputs['literal_data_bytes']>0 and inputs['literal_data_are_untrusted_proposals'] is True,'Wrong literal data scope')
    literal_data=portable_data(repository,inputs['data'],rows)
    need(len(literal_data)==inputs['data_file_count'] and sum(x['bytes']for x in literal_data)==inputs['literal_data_bytes'],'Literal data population/bytes differ')
    destination.mkdir(parents=True);inventory=destination/'SOURCE_INVENTORY.json'
    atomic(inventory,dict(schema_version=2,full_dependency_cone=rows,literal_data=literal_data,literal_data_helper_sha256=sha(HERE/'final_fap_source_data_v2.py'),portable_inputs_sha256=sha(a.inputs),portable_controller_sha256=sha(Path(__file__))))
    command=[sys.executable,str(HERE/'reproduce_final_fap_source_cold_v2.py'),'--context',str(a.context.resolve()),'--inventory',str(inventory),
      '--run',str(run),'--scratch-root',str(a.scratch_root.resolve()),'--workers',str(a.workers),'--worker-memory-gib',str(a.worker_memory_gib)]
    for root in inputs['roots']:command.extend(['--root',root])
    atomic(destination/'COMMAND.json',dict(command=command,prepared_sources=len(rows),literal_data_files=len(literal_data),literal_data_bytes=sum(x['bytes']for x in literal_data),application_object_cache=False,prepare_only=a.prepare_only))
    if a.prepare_only:print(json.dumps(dict(status='PASS_PORTABLE_SOURCE_PREPARATION_ONLY',modules=len(rows),literal_data_files=len(literal_data),literal_data_bytes=sum(x['bytes']for x in literal_data),inventory=str(inventory))));return
    subprocess.run(command,check=True)

if __name__=='__main__':main()
