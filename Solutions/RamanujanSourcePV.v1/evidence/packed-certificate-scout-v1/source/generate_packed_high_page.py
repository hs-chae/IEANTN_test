#!/usr/bin/env python3
"""Bounded first ORIGINAL high page: explicit versus128-packed, not a full rebuild."""
from pathlib import Path
import argparse,hashlib,json,re
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for data in iter(lambda:f.read(1048576),b''):h.update(data)
 return h.hexdigest()
def tree(words,lo=0):
 if len(words)==1:return '(.leaf 0x'+format(words[0],'x')+')'
 mid=len(words)//2
 return '(.branch '+str(lo+mid)+' '+tree(words[:mid],lo)+' '+tree(words[mid:],lo+mid)+')'
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();d=json.loads(a.manifest.read_text());context=json.loads((S/'BUILD_CONTEXT.json').read_text());out=a.out.resolve();need(not out.exists()and out.is_relative_to(Path(context['new_application_object_root']).resolve().parent),'fresh owned bounded page output');need(d['packed_bits']==324 and d['data_chunk']==131072 and d['records']>=131072 and d['proof_chunk']==32768,'exact original high page/chunk parameters');need(sha(d['packed_file'])==d['packed_sha256'],'original whole packed bytes pinned')
with Path(d['packed_file']).open('rb')as f:raw=f.read(131072*41)
words=[int.from_bytes(raw[i:i+41],'little')for i in range(0,len(raw),41)];need(len(words)==131072 and all(w<1<<324 for w in words),'exact original first131072words');old=d['namespace'];base='RamanujanPV.PackedHighBaseline';ns='RamanujanPV.PackedHigh128';source=out/'source';source.mkdir(parents=True);modules=[]
def emit(module,text,kind):
 path=source/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text);modules.append({'module':module,'source':str(path),'sha256':sha(path),'kind':kind})
for suffix in ['Data0000','Gaps']:
 item=next(m for m in d['modules']if m['module']==old+'.'+suffix);path=Path(item['source']);need(sha(path)==item['sha256'],'original selected written source');text=path.read_text()
 if suffix=='Data0000':need([int(x,16)for x in re.findall(r'\.leaf (0x[0-9a-f]+)',text)]==words,'every original page source word matches packed bytes')
 emit(base+'.'+suffix,text.replace(old,base),'baseline_data')
header='set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nset_option Elab.async false\n'
emit(base+'.Data','import '+base+'.Data0000\nimport RamanujanPV.QuotientCertificateCode\nnamespace '+base+'\nnoncomputable def rawNodes : Lean.RArray Nat := raw_0000\nnoncomputable def nodes := RamanujanPV.QuotientPackedDemand.unpack rawNodes\nend '+base+'\n','baseline_data')
checks='open RamanujanPV.QuotientDemandCheck\n'+header+'theorem original_first32768 : allFrom (checkEntry nodes '+base+'.gaps '+base+'.gapCount) 0 32768=true := by decide +kernel\n#print axioms original_first32768\n'
emit(base+'.Check','import '+base+'.Data\nimport '+base+'.Gaps\nnamespace '+base+'\n'+checks+'end '+base+'\n','baseline_check')
groups=[sum(w<<(324*j)for j,w in enumerate(words[i:i+128]))for i in range(0,len(words),128)];need(all((groups[i//128]>>(324*(i%128)))%(1<<324)==w for i,w in enumerate(words)),'every untrusted extraction matches original')
text='import RamanujanPV.PackedCertificateArray\nimport RamanujanPV.QuotientCertificateCode\nnamespace '+ns+'\n'+header+'noncomputable def groups : Lean.RArray Nat := '+tree(groups)+'\nnoncomputable def reader (i : Nat) : Nat := (groups.get (i/128) >>> (324*(i%128))) % (2^324)\nnoncomputable def rawNodes : Lean.RArray Nat := RamanujanPV.PackedCertificateArray.tabulate reader 17 0\nnoncomputable def nodes := RamanujanPV.QuotientPackedDemand.unpack rawNodes\nend '+ns+'\n';emit(ns+'.Data',text,'packed_data')
emit(ns+'.Check','import '+ns+'.Data\nimport '+base+'.Gaps\nnamespace '+ns+'\n'+checks+'end '+ns+'\n','packed_check')
emit(ns+'.Equality','import '+ns+'.Data\nimport '+base+'.Data\nnamespace '+ns+'\nopen RamanujanPV.QuotientDemandCheck\n'+header+'theorem every_original_page_word : allFrom (fun i=>decide (rawNodes.get i='+base+'.rawNodes.get i)) 0 131072=true := by decide +kernel\n#print axioms every_original_page_word\nend '+ns+'\n','word_identity')
proposal={'status':'UNTRUSTED_BOUNDED_FIRST_HIGH_PAGE_REPRESENTATION_PROPOSAL','original_manifest':str(a.manifest.resolve()),'original_manifest_sha256':sha(a.manifest),'original_packed_sha256':d['packed_sha256'],'original_total_records':d['records'],'page_records':131072,'checked_prefix_records':32768,'pack_size':128,'record_bits':324,'every_native_source_word_and_extraction_equal':True,'source_root':str(source),'modules':modules,'original692_data_pipeline_changed':False,'full_high_pi_proof_claimed':False,'generator_sha256':sha(__file__)};(out/'PROPOSAL.json').write_text(json.dumps(proposal,indent=2)+'\n');print(json.dumps({'status':proposal['status'],'modules':len(modules),'out':str(out)}))
