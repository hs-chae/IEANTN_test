#!/usr/bin/env python3
"""Untrusted representation proposal; all original words/predicates need kernel checks."""
from pathlib import Path
import argparse,hashlib,json
S=Path(__file__).resolve().parents[1]
def need(value,message):
 if not value:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):
 def pairs(items):
  result={}
  for key,value in items:
   need(key not in result,'duplicate JSON key');result[key]=value
  return result
 return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def tree(words,lo=0):
 if len(words)==1:return '(.leaf 0x'+format(words[0],'x')+')'
 mid=len(words)//2
 return '(.branch '+str(lo+mid)+' '+tree(words[:mid],lo)+' '+tree(words[mid:],lo+mid)+')'
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();d=read(a.manifest);context=read(a.context);out=a.out.resolve();need(not out.exists()and out.is_relative_to(Path(context['new_application_object_root']).resolve().parent),'fresh owned proposal output')
need(d['schema']=='RAMANUJAN_PACKED_DEMAND_CERTIFICATE_PROPOSAL_V1'and d['packed_bits']==324 and d['packed_bytes_per_record']==41,'original exact324-bit record format')
raw=Path(d['packed_file']).read_bytes();need(hashlib.sha256(raw).hexdigest()==d['packed_sha256']and len(raw)==d['records']*41,'complete original packed file');words=[int.from_bytes(raw[i:i+41],'little')for i in range(0,len(raw),41)];need(all(word<1<<324 for word in words),'all original word widths');old=d['namespace'];baseline='RamanujanPV.PackedControlBaseline';source=out/'source';source.mkdir(parents=True);modules=[]
def emit(module,text,kind):
 path=source/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text);modules.append({'module':module,'source':str(path),'sha256':sha(path),'kind':kind})
for entry in d['modules']:
 if entry['module'].endswith(('.Gaps','.Data'))or entry['module'].rsplit('.',1)[-1].startswith('Data'):
  path=Path(entry['source']);need(sha(path)==entry['sha256'],'original source pinned');emit(entry['module'].replace(old,baseline),path.read_text().replace(old,baseline),'baseline_data')
header='set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nset_option Elab.async false\n'
checks='open RamanujanPV.QuotientDemandCheck\n'+header+'theorem all_numeric : allFrom (checkEntry nodes '+baseline+'.gaps '+baseline+'.gapCount) 0 '+str(d['records'])+'=true := by decide +kernel\n#print axioms all_numeric\n'
emit(baseline+'.Check','import '+baseline+'.Data\nnamespace '+baseline+'\n'+checks+'end '+baseline+'\n','baseline_check')
for pack in [16,128,512]:
 ns='RamanujanPV.PackedControl'+str(pack);groups=[sum(word<<(324*j)for j,word in enumerate(words[i:i+pack]))for i in range(0,len(words),pack)]
 for i,word in enumerate(words):need((groups[i//pack]>>(324*(i%pack)))% (1<<324)==word,'proposal every original word extraction')
 depth=(len(words)-1).bit_length();text='import RamanujanPV.PackedCertificateArray\nimport RamanujanPV.QuotientCertificateCode\nimport '+baseline+'.Gaps\nnamespace '+ns+'\n'+header
 text+='noncomputable def groups : Lean.RArray Nat := '+tree(groups)+'\nnoncomputable def reader (i : Nat) : Nat := if i<'+str(len(words))+' then (groups.get (i/'+str(pack)+') >>> (324*(i%'+str(pack)+'))) % (2^324) else 0\n'
 text+='noncomputable def rawNodes : Lean.RArray Nat := RamanujanPV.PackedCertificateArray.tabulate reader '+str(depth)+' 0\nnoncomputable def nodes : Lean.RArray RamanujanPV.QuotientDemandCheck.Entry := RamanujanPV.QuotientPackedDemand.unpack rawNodes\nend '+ns+'\n';emit(ns+'.Data',text,'packed_data')
 emit(ns+'.Check','import '+ns+'.Data\nnamespace '+ns+'\n'+checks+'end '+ns+'\n','packed_check')
 equal='import '+ns+'.Data\nimport '+baseline+'.Data\nnamespace '+ns+'\nopen RamanujanPV.QuotientDemandCheck\n'+header+'theorem every_original_word : allFrom (fun i=>decide (rawNodes.get i='+baseline+'.rawNodes.get i)) 0 '+str(len(words))+'=true := by decide +kernel\n#print axioms every_original_word\nend '+ns+'\n';emit(ns+'.Equality',equal,'word_identity')
manifest={'status':'UNTRUSTED_REPRESENTATION_PROPOSAL_REQUIRES_ALL_KERNEL_CHECKS','original_manifest':str(a.manifest.resolve()),'original_manifest_sha256':sha(a.manifest),'original_packed_file':d['packed_file'],'original_packed_sha256':d['packed_sha256'],'records':len(words),'record_bits':324,'original_checker':'QuotientDemandCheck.checkEntry after QuotientPackedDemand.unpack','source_root':str(source),'modules':modules,'packing_sizes':[16,128,512],'all_native_extractions_equal_original_words':True,'native_equality_is_not_formal_acceptance':True,'generator_sha256':sha(__file__),'context':str(a.context.resolve()),'context_sha256':sha(a.context)};(out/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'status':manifest['status'],'records':len(words),'modules':len(modules),'out':str(out)}))
