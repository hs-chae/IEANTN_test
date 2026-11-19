from pathlib import Path
import json,hashlib
p=Path('review.json')
j=json.loads(p.read_text())
keys=['source_locators','derivation_check','numerical_obligations','actual_verification_receipts','retained_valid_branches','implemented_readbacks','V_status','remaining_trust','baseline_comparison']
register={}
for i,k in enumerate(keys):
 vals=[];dic={}
 for c in j['claims']:
  s=json.dumps(c[k],ensure_ascii=False,sort_keys=True)
  if s not in dic:dic[s]=len(vals);vals.append(c[k])
  c[k]=str(i)+':'+str(dic[s])
 register[str(i)]={'field':k,'values':vals}
for c in j['claims']:
 for k in ('packet_file','physical_LF_end'):
  if k=='physical_LF_end' and c['written_source'][k]!=c['written_source']['physical_LF']:continue
  c['written_source'].pop(k,None)
 y=c['propagation']
 y['matched_comparison']=c['baseline_comparison']
 y['where_it_changes_proof']=('Mellin edge; see review.md' if y['input_used']=='D02' else 'B0 proves D01; see review.md')
j['field_encoding']='Each n:k value in the registered fields refers to zero-based index k in claim_field_legend.json[n].values; propagation.matched_comparison uses the baseline_comparison register. No claim row is omitted.'
p.write_text(json.dumps(j,ensure_ascii=False,separators=(',',':'))+'\n')
Path('claim_field_legend.json').write_text(json.dumps(register,ensure_ascii=False,separators=(',',':'))+'\n')
print('review.json bytes',p.stat().st_size)
assert p.stat().st_size<2*1024*1024
