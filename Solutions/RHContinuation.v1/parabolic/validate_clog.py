#!/usr/bin/env python3
"""Fail-closed independent acceptance of the actual C→moment source replay."""
from pathlib import Path
import argparse,hashlib,json,os,re,sys
B=Path(__file__).resolve().parent

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  result={}
  for k,v in rows:need(k not in result,'duplicateJSONkey');result[k]=v
  return result
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,
  parse_constant=lambda v:(_ for _ in()).throw(ValueError('nonfiniteJSON')))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--receipt',type=Path);a=p.parse_args();need(not a.out.exists(),'fresh validator output required');O=a.run.resolve();receipt=a.receipt or O/'RESULT.json';j=read(receipt);need(j['status']=='PASS','passing replay status');need(j['schema']=='SOURCE_FIRST_C_LOG_TO_ACTUAL_PSI_NETWORK_REPLAY_V2','replay schema');need(j['validator_sha256']==sha(B/'reproduce_clog.py'),'replay validator source identity');need(j['no_prebuilt_application_objects']is True,'source-only replay');need(j['actual_child_routes']==9 and j['rejected_invalid_CLI_routes']==27,'complete active child universe');need(j['accepted_numeric_cap']=='567/800','fixed mathematical cap');need(j['final_theorem']=='RHContinuation.CLogMomentNetwork.box_psi','actual final consumer identity');need(j['OOM_events']==0,'completed OOM-free replay');need(j['source_closure_sha256']==sha(O/'SOURCE_CLOSURE.json'),'source closure digest')
source=read(O/'SOURCE_CLOSURE.json');build=read(O/'BUILD.json');need(len(source)==j['application_source_modules']and len(source)>30,'complete source count');need([r['module']for r in source]==[r['module']for r in build['modules']],'complete ordered source replay');need(len({r['module']for r in source})==len(source),'no collapsed compiler identity');need(source[-1]['module']=='Solution','final consumer actually compiled')
for s,b in zip(source,build['modules']):
 need(s['sha256']==b['source_sha256']==sha(s['source']),'actual source identity:'+s['module']);need(b['returncode']==0,'source compile returncode');need(b['memory_limit_bytes']>=16*1024**3,'declared proof memory policy')
raw=(O/'logs/CLogMomentNetwork.stdout').read_text();matches=re.findall(r"'RHContinuation.CLogMomentNetwork.box_moments' depends on axioms: \[([^\]]*)\]",raw);need(len(matches)==1,'unique actual theorem audit');need({v.strip()for v in matches[0].split(',')}=={'propext','Classical.choice','Quot.sound'},'exact standard axiom set')
for name,content in [('RHContinuation.CLogMomentNetwork.box_psi',raw),('RHSmoothingInputs.v1.challenge_box_moments',(O/'logs/Solution.stdout').read_text())]:
 matches=re.findall(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",content);need(len(matches)==1 and{v.strip()for v in matches[0].split(',')}=={'propext','Classical.choice','Quot.sound'},'composed actual consumer axiom audit:'+name)
need(j['canonical_node_wrapper']=='RHSmoothingInputs.v1.challenge_box_moments','actual canonical challenge wrapper')
need(j['remaining_analytic_inputs']==['RHSmoothingInputs.v1.box_explicit_formula','RHSmoothingInputs.v1.box_zero_estimate','BoxMellinInputs.v1.first_moment','BoxMellinInputs.v1.second_moment_identity','BoxMellinInputs.v1.stieltjes_trapezoid'],'all remaining analytic claims explicitly retained')
need(j['C_source_sha256']=='a22ee045b69b971a6fd3156ba745b3bebf7109ed98db43bf0064244e538b246c','fixed original C algorithm source')
peaks=[]
for f in (O/'logs').glob('*.resources'):
 match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',f.read_text());need(match is not None,'actual module resource receipt');peaks.append(int(match[1]))
need(j['max_Lean_peak_RSS_kib']==max(peaks),'actual measured proof peak RSS')
expected={(s,m)for s in ['native_log_workload.py','box_mellin_trapezoid.py','box_mellin_series.py']for m in[0,1,2]};actual={(r['script'],r['mode'])for r in j['numeric_rows']};need(len(j['numeric_rows'])==9 and actual==expected,'all actual child routes covered');native=[]
for r in j['numeric_rows']:
 need(r['receipt_sha256']==sha(r['receipt']),'child receipt digest');c=read(r['receipt']);need(c['python_optimization']==r['mode'],'child optimization identity');need(r['rejected_invalid_CLI_routes']==3,'each child invalidCLIcoverage');controls=read(O/(r['script'].removesuffix('.py')+'-'+str(r['mode'])+'-controls.json'));need({v['label']for v in controls}=={'missing-output','unknown-argument','existing-output'}and all(v['returncode']!=0 for v in controls),'actual rejected CLI receipts')
 if r['script']=='native_log_workload.py':
  need(c['C_source_sha256']==j['C_source_sha256']==sha(c['C_source']),'C source digest');need(c['harness_sha256']==sha(B/r['script']),'native harness digest');need([v['n']for v in c['rows']]==list(range(2,129)),'all127 input calls');need(sha(Path(r['receipt']).parent/'CLogNativeRows.lean')==sha(B/'CLogNativeRows.lean'),'actual rows equal proved rows');need(sha(Path(r['receipt']).parent/'verified_finite_log.so')==c['binary_sha256'],'nativebinarydigest');native.append(c['rows'])
 else:need(c['source_sha256']==sha(B/r['script'])and c['rational_sha256']==sha(B/'rational.py'),'directed numerical source digest')
need(native[0]==native[1]==native[2],'actualCmodeinvariance');out={'status':'PASS','python_optimization':sys.flags.optimize,'validator_sha256':sha(__file__),'source_receipt_sha256':sha(receipt),'source_modules':len(source),'active_child_routes':9,'rejected_invalid_child_routes':27,'scope':'Source-first C component and actual conditional psi-network proof; analytic source claims remain explicit open inputs.'};a.out.parent.mkdir(parents=True,exist_ok=True);temp=a.out.with_suffix(a.out.suffix+'.pending');need(not temp.exists(),'fresh atomic temporary');temp.write_text(json.dumps(out,indent=2)+'\n');os.replace(temp,a.out);print(json.dumps(out,indent=2))
