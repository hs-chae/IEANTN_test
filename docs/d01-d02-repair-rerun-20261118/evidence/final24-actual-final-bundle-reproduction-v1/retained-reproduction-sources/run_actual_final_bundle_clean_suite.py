from pathlib import Path
import hashlib,html.parser,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
T=Path(__file__).resolve().parents[1];B=T/'extracted';W='/ryu/hyunsik/playground/independence/codex/ivy'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
def pin(p):return{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def load(p):return json.loads(p.read_bytes())
class Visible(html.parser.HTMLParser):
 def __init__(self):super().__init__(convert_charrefs=True);self.body=False;self.skip=0;self.text=[]
 def handle_starttag(self,tag,attrs):
  if tag=='body':self.body=True
  if self.body and tag in['style','script']:self.skip+=1
 def handle_endtag(self,tag):
  if tag=='body':self.body=False
  if self.body and tag in['style','script']:self.skip-=1
 def handle_data(self,text):
  if self.body and not self.skip:self.text.append(text)
def visible(text):
 p=Visible();p.feed(text);return' '.join(' '.join(p.text).split())
def main():
 need(T.name=='ivy-final24-actual-bundle-repro-ldnkxgks'and B.is_dir(),'one verified actual extraction');os.chdir(B);empty=T/'empty-original-workspace';empty.mkdir();subprocess.run(['mount','--make-rprivate','/'],check=True);subprocess.run(['mount','--bind',str(empty),W],check=True);subprocess.run(['mount','-o','remount,bind,ro',W],check=True)
 probes=[]
 for flags in [[],['-I','-S']]:
  code="try:\n open('/ryu/hyunsik/playground/independence/codex/ivy/AGENTS.md','rb').read()\nexcept (FileNotFoundError,PermissionError):\n print('PASS_ORIGINAL_WORKSPACE_MASK_DENIES_READ')\nelse:\n raise ValueError('ORIGINAL_WORKSPACE_WAS_READABLE')";argv=[sys.executable,'-B',*flags,'-c',code];r=subprocess.run(argv,capture_output=True,text=True);need(r.returncode==0 and r.stdout.strip()=='PASS_ORIGINAL_WORKSPACE_MASK_DENIES_READ','ordinary and isolated child read denial');probes.append({'argv':argv,'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
 work=B/'reproduction-work';work.mkdir(exist_ok=False);shutil.copytree(B/'frontiers',work/'frontiers');report=work/'report';report.mkdir();paper=work/'paper';ledger=work/'ledger';logs=T/'clean-suite-evidence';logs.mkdir();env=dict(os.environ,IEANTN_SOURCE_ROOT=str(B),IEANTN_SOURCE_MAP=str(B/'PUBLIC_SOURCE_MAP.json'),PYTHONDONTWRITEBYTECODE='1',PYTHONNOUSERSITE='1');env.pop('PYTHONPATH',None)
 commands=[('report',[sys.executable,'-I','-B',str(B/'reproduction/report-tools/render_main_report_complete_v4.py'),'--data',str(B/'ALL24_PUBLIC_SCIENTIFIC_STATUS.json'),'--font',str(B/'fonts/STIXGeneral.ttf'),'--exposition',str(B/'paper/ANALYTIC_ENGINE_EXPOSITION.html'),'--comparison-html',str(B/'evidence/study/coordinator-private/twentyfour-normalized-frontiers-v1/REPORT.html'),'--source-map',str(B/'PUBLIC_SOURCE_MAP.json'),'--public-root',str(B),'--out',str(report/'FINAL_REPORT.html')]),('paper',[sys.executable,'-I','-B',str(B/'reproduction/reproduce_paper.py'),'--bundle-root',str(B),'--out',str(paper)]),('ledger',[sys.executable,'-I','-B',str(B/'reproduction/build_final24_actual_ledger.py'),'--selection',str(B/'reproduction/FINAL24_ACTUAL_RESULT_SELECTION.json'),'--source-map',str(B/'PUBLIC_SOURCE_MAP.json'),'--public-root',str(B),'--require-mapped','--out',str(ledger)]),('analysis',[sys.executable,'-B',str(work/'frontiers/reproduce_analysis.py')])];records=[]
 for name,argv in commands:
  start=time.monotonic();r=subprocess.run(argv,cwd=B,env=env,capture_output=True,text=True);stdout=logs/(name+'.stdout');stderr=logs/(name+'.stderr');stdout.write_text(r.stdout);stderr.write_text(r.stderr);records.append({'name':name,'argv':argv,'returncode':r.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':pin(stdout),'stderr':pin(stderr)});(logs/'PARTIAL.json').write_text(json.dumps({'status':'FOUR_DOCUMENTED_ACTUAL_PIPELINES_IN_PROGRESS','records':records,'old_workspace_mask_applies_to_all_descendants':True},indent=2)+'\n')
 need(all(x['returncode']==0 for x in records),'all four documented pipelines must complete');actual=(report/'FINAL_REPORT.html').read_text();accepted=(B/'report.html').read_text();math=lambda t:re.findall(r'<math\b[^>]*>.*?</math>',t,re.S);svg=lambda t:re.findall(r'<svg\b[^>]*>.*?</svg>',t,re.S);reportchecks={'all_MathML_bytes_identical':math(actual)==math(accepted),'MathML_count':len(math(actual)),'all_three_inline_SVG_bytes_identical':svg(actual)==svg(accepted),'complete_visible_body_text_identical':visible(actual)==visible(accepted)}
 (logs/'REPORT_BODY_CHECK.json').write_text(json.dumps(reportchecks,indent=2)+'\n');need(reportchecks['all_MathML_bytes_identical']and reportchecks['all_three_inline_SVG_bytes_identical']and reportchecks['complete_visible_body_text_identical'],'complete report visible mathematical content and figures')
 p=load(paper/'RECEIPT.json');need(p['same_mathematical_article']is True and p['MathML_expressions']==138,'whole paper article and138MathML');canonical=B/'evidence/study/evidence/final24-actual-resource-ledger-v1/FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json';rebuilt=ledger/'FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json';need(rebuilt.read_bytes()==canonical.read_bytes(),'exact all24 actual resource ledger JSON')
 accepted_data=load(B/'frontiers/FINITE_EXPLICIT_FUNCTIONS.json');new_data=load(work/'frontiers/FINITE_EXPLICIT_FUNCTIONS.json');need(new_data['bounds']==accepted_data['bounds']and len(new_data['bounds'])==15861,'all15861 complete source function bodies identical');need((work/'frontiers/ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes()==(B/'frontiers/ALL24_SOURCE_BOUND_OBJECTS.json').read_bytes(),'all11411 complete source collection byte-identical');pipeline=load(work/'frontiers/ACTUAL_SEQUENTIAL_ANALYSIS_REGENERATION.json');run=load(Path(pipeline['receipt']['path']));need(len(run['commands'])==7 and all(x['returncode']==0 for x in run['commands']),'all7 actual sequential commands completed')
 result={'status':'PASS_ACTUAL_FINAL_BUNDLE_DOCUMENTED_REPORT_PAPER_LEDGER_AND_SEVEN_STEP_ANALYSIS_WITH_ALL_CHILDREN_ORIGINAL_WORKSPACE_MASKED','source':pin(Path(__file__)),'bundle':str(B),'records':records,'denial_child_probes':probes,'private_mount_namespace':os.readlink('/proc/self/ns/mnt'),'old_workspace_mask_mountinfo':[s for s in Path('/proc/self/mountinfo').read_text().splitlines()if s.split()[4]==W],'report_body_checks':reportchecks,'paper_article_and138MathML_identical':True,'ledger_JSON_byte_identical':True,'all15861_complete_function_bodies_identical':True,'all11411_source_collection_bytes_identical':True,'seven_step_pipeline_receipt':pin(Path(pipeline['receipt']['path'])),'new_ANT_workload_Lean_model_or_source_first_PV':False};(logs/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'receipt':pin(logs/'RESULT.json')}))
if __name__=='__main__':main()
