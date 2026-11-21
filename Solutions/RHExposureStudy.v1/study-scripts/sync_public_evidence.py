#!/usr/bin/env python3
"""Copy explicit mathematical sources/evidence; never coordinator state or auth."""
from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parents[1];D=Path('/data/ivy-rh-propagation-20261120');S=R/'network/Solutions/RHExposureStudy.v1';copied=[]
def cp(src,dst):
 if not src.is_file()or src.is_symlink():raise ValueError('exact regular public source required:'+str(src))
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);copied.append({'source':str(src),'path':dst.relative_to(S).as_posix(),'bytes':dst.stat().st_size,'sha256':hashlib.sha256(dst.read_bytes()).hexdigest()})
def tree(src,dst):
 for p in src.rglob('*'):
  if not p.is_file():continue
  rel=p.relative_to(src)
  if any(x in rel.parts for x in ['objects','__pycache__','.lake','root','dependency-view']):continue
  if p.suffix in ['.olean','.pyc','.o','.so','.a','.zip']:continue
  if p.name in ['finite_ram_replay','finite_ram','coefficient_native']:continue
  cp(p,dst/rel)
for name in ['final-NL','final-IEANTN','final-full-Ramanujan','report-reader-v1','fresh-report-reader-v1','fresh-report-reader-v2','fresh-report-reader-v3','final-report-source-fidelity-v1','final-report-source-fidelity-v2','postlock-forward243','post-lock-forward243-independent']:
 p=D/'review'/name
 if p.exists():tree(p,S/'review'/name)
tree(D/'setup/LN_INDEPENDENT_AUDIT',S/'evidence/LNsource')
for p in (R/'scripts').glob('*.py'):cp(p,S/'study-scripts'/p.name)
for p in (R/'reports').iterdir():
 if p.is_file():cp(p,S/'reports'/p.name)
for name in ['RESULTS.json','OUTCOMES.csv','FINAL_FACTS.json','POST_RUN_INITIAL_INPUT_RECHECK.json','DISCOVERY_SERVICE_CLOSEOUT.json']:
 if (R/'publication'/name).exists():cp(R/'publication'/name,S/'ledgers'/name)
for name in ['HISTORICAL_QRH_FUNCTIONS_INTERNAL.json','LITERATURE_FLOOR_INTERNAL.json','BASELINE_INTERNAL.json','FULL_EXPOSURE_ADDITIONS.json','UNTRACKED_PRIVACY_REVIEW_INTERNAL.json','REQUEST_SCHEMA_DEFECT_OBSERVED.json','SOURCE_BROKER_ALLMODE_ACCEPTANCE.json']:
 cp(D/'setup'/name,S/'ledgers'/name.replace('_INTERNAL',''))
cp(D/'observation/SUMMARY.json',S/'evidence/resource-observation/SUMMARY.json');cp(D/'observation/RESOURCE_OBSERVATIONS.jsonl',S/'evidence/resource-observation/RESOURCE_OBSERVATIONS.jsonl')
for arm in ['NL_RH','IEANTN_RH']:
 for name in ['PREFLIGHT.json','os.stdout','os.stderr']:
  cp(D/'setup'/('preflight-'+arm+'-v2')/name,S/'evidence/preflight'/arm/name)
for name in ['locked-full-replay-v1','locked-NL-replay-v1','mertens-relocated-replay-v1','generic-context-relocation-v1']:
 p=D/'post-lock-verification'/name
 for f in ['RESULT.json','REPLAY_RESULT.json','BOOTSTRAP_RECEIPT.json','stdout','stderr']:
  if (p/f).exists():cp(p/f,S/'evidence/replays'/name/f)
cp(D/'clean-input-reconstruction-v1-RECONSTRUCTION.json',S/'evidence/CLEAN_INPUT_RECONSTRUCTION.json')
tree(R/'evaluator-private/checkpoints',S/'evidence/timed-checkpoints')
# These are mathematical-task/runtime configurations, not private model sessions.
for name in ['NEUTRAL_CHECKPOINT_REVIEW.json','NEUTRAL_PUSH_VERIFIED.json','RESULT_INTEGRATION_PLAN.json']:
 if (R/'publication'/name).exists():cp(R/'publication'/name,S/'evidence/publication'/name)
(S/'ledgers/PUBLIC_COPY_RECEIPT.json').write_text(json.dumps({'selection':'Explicit mathematical source/result/review/protocol paths; no memory, coordinator conversation, credentials or raw provider session copied','files':copied},indent=2)+'\n')
print(len(copied),'explicit public evidence copies',sum(r['bytes']for r in copied),'bytes')
