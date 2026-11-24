#!/usr/bin/env python3
"""Remove only byte-verified duplicate regenerated suggestions after a completed reproduction."""
import argparse,hashlib,json,pathlib,sys

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',required=True);args=ap.parse_args();root=pathlib.Path(args.run).resolve()
 receipt=root/'REPRODUCTION.json'
 if not receipt.is_file():raise ValueError('No successful reproduction receipt')
 record=json.load(receipt.open())
 if record.get('status')!='PASS_REGENERATED_CERTIFICATES_AND_FRESH_LEAN_REPLAY':raise ValueError('Reproduction has not passed')
 target=root/'regenerated'
 if target.is_symlink() or target.resolve()!=root/'regenerated' or not target.is_dir():raise ValueError('Unsafe/missing owned regeneration directory')
 expected={r['module']+'.lean':r['regenerated_sha256'] for r in record['generated_sources']}
 actual=list(target.iterdir())
 if any(p.is_symlink() or not p.is_file() for p in actual):raise ValueError('Unexpected non-file in cleanup directory')
 if set(p.name for p in actual)!=set(expected)|{'CELL_DATA.json'}:raise ValueError('Unexpected regeneration directory contents')
 for name,sha in expected.items():
  if digest(target/name)!=sha:raise ValueError('Generated source changed: '+name)
 plan=[{'path':str(p),'bytes':p.stat().st_size,'sha256':digest(p),'reason':'Duplicate deterministic numerical suggestions; essential exact coefficients, generator, accepted Lean source and proof artifacts retained'} for p in actual]
 report={'status':'VERIFIED_OWNED_TARGETS_BEFORE_DELETION','reproduction_receipt_sha256':digest(receipt),'targets':plan,'bytes':sum(r['bytes'] for r in plan),'retained':['original candidate','generators','accepted Lean sources','fresh source/object proof artifacts','execution and axiom receipts','partition and generation logs']}
 (root/'CLEANUP_PREVIEW.json').write_text(json.dumps(report,indent=2)+'\n')
 for p in actual:p.unlink()
 target.rmdir()
 if target.exists():raise RuntimeError('Cleanup target still exists')
 report['status']='PASS_DUPLICATE_REGENERABLE_SUGGESTIONS_REMOVED'
 (root/'CLEANUP.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'status':report['status'],'bytes_removed':report['bytes'],'run':str(root)}))
if __name__=='__main__':
 try:main()
 except Exception as exc:print(type(exc).__name__+': '+str(exc),file=sys.stderr);sys.exit(1)
