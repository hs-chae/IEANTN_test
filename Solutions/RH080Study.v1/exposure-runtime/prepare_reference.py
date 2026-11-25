#!/usr/bin/env python3
"""Materialize a fresh fixture reference from public templates and explicit roots.

Creates no research lock, invokes no account/model, and copies no mounted data.
Every assigned source tree must match its full frozen per-file inventory later
when launch_fixture.py runs the unchanged gate.
"""
import argparse,hashlib,json,os,tempfile
from pathlib import Path
from strict_json import read


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--template',choices=['primary','followup-V0','followup-V1'],required=True)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--toolchain',type=Path,required=True)
    ap.add_argument('--packages',type=Path,required=True)
    ap.add_argument('--generic-source-root',type=Path,required=True)
    ap.add_argument('--corpus',type=Path,required=True)
    ap.add_argument('--representation',type=Path,required=True)
    ap.add_argument('--support',type=Path)
    a=ap.parse_args();R=a.repository.resolve(strict=True);E=R/'Solutions/RH080Study.v1/exposure-runtime'
    need(not a.root.exists(),'Fresh reference root required');root=a.root.resolve();need(not root.is_relative_to(R),'Reference root must be outside source');root.mkdir(parents=True)
    template=E/'references'/(a.template+'.json');spec=read(template);runtime=dict(spec['runtime']);mounts=[]
    (root/'trees').mkdir()
    for index,row in enumerate(spec['mounts']):
        target=row['target']
        if target=='/opt/lean':source=a.toolchain
        elif target.startswith('/generic/lib/'):source=a.packages/target.rsplit('/',1)[1]/'.lake/build/lib/lean'
        elif target.startswith('/generic/source/'):source=a.generic_source_root/target.rsplit('/',1)[1]
        elif target=='/corpus/literature':source=a.corpus
        elif target=='/representation':source=a.representation
        elif target=='/source_pv':need(a.support is not None,'Explicit proof-support root required');source=a.support
        else:raise ValueError('Unexpected frozen mount target')
        source=source.resolve(strict=True);need(source.is_dir(),'Assigned source is not a directory')
        frozen=E/'references'/row['tree_file'];need(sha(frozen)==row['tree_sha256'],'Public reference tree changed')
        tree=read(frozen);tree['root']=str(source)
        copied=root/'trees'/(str(index).zfill(2)+'.json');copied.write_text(json.dumps(tree,indent=2)+'\n')
        mounts.append({k:v for k,v in row.items() if k not in ['tree_file','tree_sha256']}|dict(source=str(source),manifest=dict(path=str(copied),sha256=sha(copied))))
    runtime['mounts']=mounts;runtime_path=root/'runtime.json';runtime_path.write_text(json.dumps(runtime,indent=2)+'\n')
    protocol=R/spec['protocol_repository_path'];need(sha(protocol)==spec['protocol_sha256'],'Frozen public protocol differs')
    packet=root/'packet';packet.mkdir();task=packet/'TASK.md';task.write_text('NEUTRAL PORTABLE SOURCE-PREPARED FIXTURE ONLY. No real model inference.\n')
    manifest=root/'packet.json';manifest.write_text(json.dumps(dict(root=str(packet),files={'TASK.md':sha(task)}),indent=2)+'\n')
    pin=lambda p:dict(path=str(p),sha256=sha(p))
    lock=dict(schema='RH080_TRIAL_LOCK_V1',reviewed_by='/root',fixture=True,condition=spec['condition'],task=spec['task'],replicate=spec['replicate'],
      protocol=pin(protocol),runtime=pin(runtime_path),packet_manifest=pin(manifest),out=str(root/'not-launched'),
      scope='Additive source-prepared reference for an authorized NOAUTH fixture; no research execution or original-outcome change. Full tree checks occur in launch_fixture before execution.')
    lock_path=root/'REFERENCE_FIXTURE_LOCK.json';lock_path.write_text(json.dumps(lock,indent=2)+'\n')
    receipt=dict(status='PREPARED_PUBLIC_TEMPLATE_REFERENCE_NOT_EXECUTION_ACCEPTANCE',reference_lock=str(lock_path),reference_lock_sha256=sha(lock_path),
                public_template_sha256=sha(template),controller_sha256=sha(Path(__file__)),model_calls=0,full_source_trees_checked=False)
    (root/'PREPARATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))


if __name__=='__main__':main()
