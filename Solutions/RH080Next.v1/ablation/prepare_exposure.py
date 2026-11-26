#!/usr/bin/env python3
"""Prepare matched exposure from exact previously accepted proof banks.
No inference; no old experimental outcome is modified.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
R=Path(__file__).resolve().parents[3];S=R/'Solutions/RH080Next.v1';HERE=Path(__file__).resolve().parent
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(items):
 d={}
 for k,v in items:
  need(k not in d,'Duplicate JSON key');d[k]=v
 return d
def load(p):return json.loads(p.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def save(p,value):
 need(not p.exists(),'Fresh artifact required '+str(p));p.parent.mkdir(parents=True,exist_ok=True);tmp=p.with_name('.'+p.name+'.tmp')
 with tmp.open('x')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 try:os.link(tmp,p)
 finally:tmp.unlink()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--gaussian-run',type=Path,required=True);p.add_argument('--population-run',type=Path,required=True);p.add_argument('--work',type=Path,required=True);p.add_argument('--flat-facts',type=Path,required=True);a=p.parse_args();need(not a.work.exists(),'Fresh preparation directory required');a.work.mkdir();context=load(a.context);need(sha(Path(context['compiler']))==context['compiler_sha256'],'Compiler identity')
index={};receipt_pins=[]
for bank,expected in [(a.gaussian_run,'PASS_COMPLETE_SCALED40_CERTIFICATE_TRUE_FOURIER_CMS_V4_CONSUMERS'),(a.population_run,'PASS_COMPLETE_SOURCE_FIRST_NUMERICAL_FOURIER_EVENTUAL_PRIME_POPULATION_AND_MATCHED_CONTROL')]:
 plan=load(bank/'PLAN.json');result=load(bank/'RESULT.json');need(result['status']==expected,'Unaccepted source bank');need(result['plan_sha256']==sha(bank/'PLAN.json'),'Plan receipt mismatch');need(set(result['standard_axioms'])<={'propext','Classical.choice','Quot.sound'},'Nonstandard axiom bank');records={x['module']:x for x in result['commands']};receipt_pins.append({'run':str(bank),'plan_sha256':sha(bank/'PLAN.json'),'result_sha256':sha(bank/'RESULT.json')})
 for row in plan['modules']:
  n=row['module'];record=records[n];need(record['returncode']==0,'Failed source module');origin=Path(row.get('origin',row.get('original')));source=bank/'source'/(n.replace('.','/')+'.lean');obj=bank/'objects'/(n.replace('.','/')+'.olean');need(sha(origin)==sha(source)==row['source_sha256']==record['source_sha256'],'Changed source '+n);need(sha(obj)==record['object_sha256'],'Changed proof object '+n)
  for ext in ['stdout','stderr']:
   log=bank/'logs'/(n.replace('.','_')+'.'+ext);need(sha(log)==record[ext+'_sha256'],'Changed compiler log '+n);need(re.search(r'PANIC|error(?:\([^)]*\))?:',log.read_text(),re.I)is None,'Compiler diagnostic '+n)
  item={'module':n,'origin':origin,'source':source,'object':obj,'source_sha256':sha(source),'object_sha256':sha(obj),'imports':row['imports'],'bank':str(bank)}
  if n in index:need(index[n]['source_sha256']==item['source_sha256'],'Conflicting written source identity '+n)
  index[n]=item

def closure(roots):
 seen=set()
 def visit(n):
  if n in seen or n.split('.')[0]in GENERIC:return
  need(n in index,'Missing accepted application dependency '+n);seen.add(n)
  for dep in index[n]['imports']:visit(dep)
 for n in roots:visit(n)
 return seen
kernel=closure(['Scaled40ActualConsumers','PopulationMatchedControl']);source=closure(['Scaled40ActualConsumers','PopulationMatchedControl','PopulationActualConsumers']);need(kernel<=source,'Unmatched mathematical support');need(not any(n.startswith('GoldbachDirect')or n.endswith('SourceFinal')for n in kernel),'Source-first implementation leaked into kernel support')
# The mathematical theorem pack uses only the kernel control in B/C/D.
pack=a.work/'pack';(pack/'source').mkdir(parents=True);(pack/'objects').mkdir()
for n in sorted(kernel):
 dest=pack/'objects'/(n.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(index[n]['object'],dest)
code='''import Scaled40ActualConsumers
import PopulationMatchedControl
set_option autoImplicit false
noncomputable section
namespace RH080Exposure.Estimates

theorem gaussian (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) : RHAsymptoticGaussian.v4.population_curve :=
  RH080Next.Scaled40Canonical.actual_population_curve hCMS hRH

theorem sparse (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    RHWeightedPopulation.v1.sparse_curve :=
  RHWeightedPopulation.v1.challenge_sparse_curve hUniform hRH
    (RH080Next.PopulationCanonical.kernel_only_sparse_witness hNorm)

theorem flat (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    RHWeightedPopulation.v1.flat_curve :=
  RHWeightedPopulation.v1.challenge_flat_curve hUniform hRH
    (RH080Next.PopulationCanonical.kernel_only_flat_witness hNorm)

#print axioms gaussian
#print axioms sparse
#print axioms flat
end RH080Exposure.Estimates
'''
file=pack/'source/RH080EstimatePack.lean';file.write_text(code);env=dict(os.environ,LEAN_PATH=str(pack/'objects')+':'+context['generic_lean_path']);start=time.monotonic();cmd=[context['compiler'],'-j1','--root='+str(file.parent),'-o',str(pack/'objects/RH080EstimatePack.olean'),str(file)]
with(pack/'stdout').open('x')as out,(pack/'stderr').open('x')as err:proc=subprocess.run(cmd,env=env,stdout=out,stderr=err)
text=(pack/'stdout').read_text()+'\n'+(pack/'stderr').read_text();need(proc.returncode==0 and re.search(r'PANIC|error:',text,re.I)is None,'Estimate pack did not compile')
for name in ['gaussian','sparse','flat']:
 matches=re.findall(r"'RH080Exposure.Estimates\."+name+r"' depends on axioms: \[([^\]]*)\]",text);need(len(matches)==1 and {s.strip()for s in matches[0].split(',')if s.strip()}<={'propext','Classical.choice','Quot.sound'},'Pack theorem axiom audit')
save(pack/'COMPILED.json',{'status':'PASS_KERNEL_ONLY_ESTIMATE_PACK','command':cmd,'seconds':time.monotonic()-start,'source_sha256':sha(file),'object_sha256':sha(pack/'objects/RH080EstimatePack.olean'),'stdout_sha256':sha(pack/'stdout'),'stderr_sha256':sha(pack/'stderr'),'source_PV':False})
# Before any inference, expose the full selected statement/definition universe identically.
facts=load(a.flat_facts/'RESULT.json')
need(facts['status']=='PASS_COMPLETE_SELECTED_COMPILER_STATEMENT_CORPUS_NOT_A_SOURCE_CLAIM_AUDIT','Incomplete fact export')
need(set(facts['modules'])==source|{'RH080EstimatePack'},'Fact corpus differs from full selected exposure universe')
need(facts['compiler_sha256']==context['compiler_sha256'],'Fact compiler mismatch')
for filename,key in [('FLAT_FACTS.json','statement_json_sha256'),('FLAT_FACTS.txt','statement_text_sha256'),*([('TERM_NODES.json','exact_term_nodes_sha256')]if 'exact_term_nodes_sha256'in facts else [])]:
 need(sha(a.flat_facts/filename)==facts[key],'Changed shared mathematical inventory')
need(sha(a.flat_facts/'ExportFacts.lean')==facts['export_source_sha256'],'Changed actual export source')
save(a.work/'SHARED_FACTS.json',dict(status='PASS_EXACT_SHARED_STATEMENT_AND_DEFINITION_CORPUS',export=facts,selection_is_source_claim_audit=False,model_calls=0))
# Every arm sees the same executable numerical source, including A.
for arm in ['A_flat','B_named','C_network','D_source_PV']:
 root=a.work/'supports'/arm;root.mkdir(parents=True)
 for filename in ['FLAT_FACTS.json','FLAT_FACTS.txt']+(['TERM_NODES.json']if 'exact_term_nodes_sha256'in facts else []):
  os.link(a.flat_facts/filename,root/filename)
 shutil.copyfile(a.work/'SHARED_FACTS.json',root/'SHARED_FACTS.json')
 for filename in ['population_norm.c','flat_population_norm.c']:shutil.copyfile(S/'pv'/filename,root/filename)
 names=set()if arm=='A_flat'else(source if arm=='D_source_PV'else kernel)
 for n in sorted(names):
  target=root/'objects'/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(index[n]['object'],target)
  if arm in ['C_network','D_source_PV']:
   target=root/'source'/(n.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(index[n]['source'],target)
 if arm!='A_flat':
  shutil.copyfile(pack/'objects/RH080EstimatePack.olean',root/'objects/RH080EstimatePack.olean')
  (root/'ESTIMATE_NAMES.md').write_text('Import RH080EstimatePack. The verified named estimates are RH080Exposure.Estimates.gaussian, .sparse and .flat. Their exact hypotheses and numerical facts are the common packet facts. B exposes compiled dependencies and type inspection; no authored graph or solution-source tree is supplied. These kernel estimates are not source-first PV.\n')
 if arm in ['C_network','D_source_PV']:
  shutil.copyfile(file,root/'source/RH080EstimatePack.lean');save(root/'GRAPH.json',{'nodes':[{'module':n,'imports':index[n]['imports'],'source':'source/'+n.replace('.','/')+'.lean'}for n in sorted(names)],'program_proof_addition':sorted(source-kernel)if arm=='D_source_PV'else[]})
 save(root/'EXPOSURE.json',{'condition':arm,'application_modules':sorted(names),'source_first_added_modules':sorted(source-kernel)if arm=='D_source_PV'else[],'same_mathematical_facts':True,'original_large_FFT_PV_included':False})
save(a.work/'PREPARATION_RESULT.json',{'status':'PASS_EXACT_ACCEPTED_SUPPORT_PREPARATION_NO_INFERENCE','kernel_modules':len(kernel),'source_modules':len(source),'source_first_addition':sorted(source-kernel),'source_banks':receipt_pins,'model_calls':0,'pack_source_sha256':sha(file),'shared_facts_sha256':sha(a.work/'SHARED_FACTS.json'),'protocol_sha256':sha(HERE/'PROTOCOL.json'),'sources':[{'module':n,'source_sha256':index[n]['source_sha256'],'object_sha256':index[n]['object_sha256']}for n in sorted(source)]});print('PASS_PREPARED_SUPPORT_NO_INFERENCE',len(kernel),len(source))
