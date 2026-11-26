#!/usr/bin/env python3
"""Validate sealed exact-lock evidence; no mathematical novelty score or primary promotion."""
import argparse
from pathlib import Path
import run_review as common


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--bundle',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    bundle=args.bundle.resolve();manifest=common.load(bundle/'MANIFEST.json')
    common.need(manifest['status']=='SEALED_SUPPLEMENTAL_EVIDENCE_NOT_PRIMARY_RECLASSIFICATION','Wrong manifest scope')
    common.need(manifest['new_primary_successes']==0 and manifest['original_primary_admissible']==3 and manifest['original_primary_censored']==13,'Original outcomes reclassified')
    members=manifest['members'];names=[r['path'] for r in members]
    common.need(len(names)==len(set(names)),'Duplicate written member identities')
    actual={str(p.relative_to(bundle))for p in bundle.rglob('*')if p.is_file() and p!=bundle/'MANIFEST.json'}
    common.need(actual==set(names),'Missing or unlisted sealed artifact')
    for row in members:
        p=bundle/row['path'];common.need(p.resolve().is_relative_to(bundle) and not p.is_symlink() and p.is_file(),'Invalid sealed path')
        common.need(common.sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],'Sealed artifact differs '+row['path'])
    locked=manifest['locked_rows'];common.need(len(locked)==len({r['trial']for r in locked})==13,'Exact13 censored locks required')
    for row in locked:
        root=bundle/'locked_payloads'/row['trial'];common.need(row['primary_eligible'] is False,'Censored row promoted')
        common.need(common.sha(root/'LOCK.json')==row['lock_sha256'],'Original lock bytes differ')
        files=common.load(root/'LOCK.json')['files'];common.need(files==row['files'],'Collapsed original payload scope')
        for file in files:common.need(common.sha(root/file['path'])==file['sha256'],'Original payload changed')
    interpretation=common.load(bundle/'evidence/ALL16_MATHEMATICAL_INTERPRETATION.json')
    adapter=common.load(bundle/'REPORT_EXPOSURE_ROWS.json');rows=interpretation['rows']
    common.need(len(rows)==len({r['trial']for r in rows})==16 and sum(r['primary_eligible']for r in rows)==3,'Exact all16 mathematical reading required')
    common.need(interpretation['new_primary_successes']==0 and interpretation['external_model_inference_calls']==0,'Unexpected new research/status')
    common.need(adapter['interpretation_sha256']==common.sha(bundle/'evidence/ALL16_MATHEMATICAL_INTERPRETATION.json'),'Adapter not exact reading')
    common.need({r['id']for r in adapter['rows']}=={r['trial']for r in rows} and len(adapter['rows'])==16,'Report omitted or collapsed rows')
    runtime=common.load(bundle/'OFFLINE_DEPENDENCIES.json')
    common.need(runtime['same_original_runtime_for_all13'] is True and runtime['runtime_sha256']=='23c22ffbd40173ce027d945da1be3141def8e58103b7622f2ffd7dc3999c436a','Common originalD runtime differs')
    common.need(common.sha(bundle/'evidence/ORIGINAL_COMMON_D_RUNTIME.json')==runtime['runtime_sha256'],'Original runtime bytes differ')
    common.save(args.output,dict(status='PASS_SEALED_EXACT13_LOCKS_ALL16_INTERPRETATIONS_UNCHANGED_PRIMARY',
        members=len(members),source_modules=manifest['source_modules'],manifest_sha256=common.sha(bundle/'MANIFEST.json'),
        validator_sha256=common.sha(Path(__file__)),new_primary_successes=0))
    print('PASS sealed13exactlocks/all16readings; primary outcomes unchanged')


if __name__=='__main__':main()
