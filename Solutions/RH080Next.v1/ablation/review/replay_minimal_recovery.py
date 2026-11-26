#!/usr/bin/env python3
"""Reproduce the exact8,329byte locked file from three original literal write records.

The recorded commands are DATA. Only the previously published whitelisted string
interpreter runs; researcher Python, shell commands and model inference do not.
"""
import argparse,hashlib
from pathlib import Path
import run_review as common
from recover_supplemental import recorded_string_versions
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--trace',type=Path,default=HERE/'supplemental_attempts_v1/recovery/ORIGINAL_THREE_WRITE_EVENTS.jsonl')
    ap.add_argument('--locked',type=Path,default=HERE/'supplemental_evidence_v1/locked_payloads/prime_index-D_source_PV-r0/GrowingRank.lean')
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    wanted='e5397297b11a6f77acd79ae4f32c6e55ca8d4e360480106202c5693035ebb9e4'
    common.need(common.sha(args.locked)==wanted,'Exact locked source identity differs')
    matches=[v for v in recorded_string_versions(args.trace)if hashlib.sha256(v['bytes']).hexdigest()==wanted]
    common.need(len(matches)==1 and matches[0]['bytes']==args.locked.read_bytes(),'Literal write-record recovery does not reproduce locked bytes')
    common.save(args.output,dict(status='PASS_EXACT_LOCK_FROM_ORIGINAL_THREE_LITERAL_WRITE_RECORDS',
        source_sha256=wanted,bytes=len(matches[0]['bytes']),trace_sha256=common.sha(args.trace),
        interpreter_sha256=common.sha(HERE/'recover_supplemental.py'),controller_sha256=common.sha(Path(__file__)),
        researcher_code_executed=False,external_model_inference_calls=0,original_outcomes_changed=False))
    print('PASS exact8329byteLOCK from3literal original write records')


if __name__=='__main__':main()
