#!/usr/bin/env python3
"""Compare every exact locked declared type/axiom/dependency across the two replays."""
import argparse,json
from pathlib import Path
import run_review as common
HERE=Path(__file__).resolve().parent


def normalized(table):
    rows=table['declarations'];common.need(len(rows)==len({r['declaration']for r in rows}),'Collapsed written declaration names')
    return {r['declaration']:dict(kind=r['kind'],type=r['type'],axioms=sorted(r['axioms']),
              direct_dependencies=sorted(r['direct_dependencies']))for r in rows}


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--clean',required=True,type=Path)
    ap.add_argument('--archive',type=Path,default=HERE/'supplemental_evidence_v1/replay_evidence')
    ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    result=common.load(args.clean/'RESULT.json');common.need(result['status']=='PASS_PORTABLE_COMMON169_PLUS_ALL13_LOCKED15_LEAN_SOURCE_COLD_STD3','Actual completed portable proof run required')
    rows=[]
    for trial in result['rows']:
        for item in trial['exports']:
            module=item['module'];a=args.archive/trial['trial']/'submission'/('EXPORT.'+module+'.json')
            b=args.clean/'trials'/trial['trial']/'source'/('EXPORT.'+module+'.json')
            before=common.load(a);after=common.load(b)
            common.need(normalized(before)==normalized(after),'Declared types, axioms or proof dependencies differ '+trial['trial']+'/'+module)
            rows.append(dict(trial=trial['trial'],module=module,declarations=len(after['declarations']),original_export_sha256=common.sha(a),clean_export_sha256=common.sha(b)))
    common.need(len(rows)==15 and len({r['trial']for r in rows})==13,'Exact all13/15 source universe required')
    common.save(args.output,dict(status='PASS_ALL13_LOCKED15_FULL_EXPORTS_IDENTICAL_TYPES_AXIOMS_DEPENDENCIES',
        rows=rows,source_modules=15,declarations=sum(r['declarations']for r in rows),
        clean_result_sha256=common.sha(args.clean/'RESULT.json'),controller_sha256=common.sha(Path(__file__)),
        primary_outcomes_changed=False,new_research_inference=False))
    print('PASS every declared type/axiom/dependency identical across original-runtime and portable source-cold replay')


if __name__=='__main__':main()
