"""Offline regeneration of the unchanged source-correct mathematical exposition."""
from pathlib import Path
import argparse,hashlib,json,re,shutil,subprocess,sys

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(argv,out):
 r=subprocess.run(argv,capture_output=True);(out.with_suffix('.stdout')).write_bytes(r.stdout);(out.with_suffix('.stderr')).write_bytes(r.stderr);need(r.returncode==0,'paper CLI failed: '+str(out));return {'argv':argv,'returncode':r.returncode,'stdout_sha256':sha(out.with_suffix('.stdout')),'stderr_sha256':sha(out.with_suffix('.stderr'))}
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--bundle-root',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();b=a.bundle_root.resolve();out=a.out.resolve();need(not out.exists(),'fresh owned paper-regeneration output');out.mkdir(parents=True)
 deps=json.loads((b/'reproduction/PAPER_DEPENDENCY_SOURCE_RECEIPT.json').read_bytes());wheels=[]
 for q in deps['wheels']:
  f=b/'reproduction/paper-wheels'/q['wheel'];need(f.is_file() and sha(f)==q['sha256'] and f.stat().st_size==q['bytes'],'exact pinned offline paper wheel');wheels.append(str(f))
 work=out/'work';(work/'scripts').mkdir(parents=True);(work/'reports/fonts').mkdir(parents=True);(work/'paper').mkdir();(out/'paper').mkdir();inputs=[]
 for name in ['build_final_report.py','embed_offline_math_font.py','final_report.css']:
  f=b/'reproduction/paper-tools'/name;shutil.copyfile(f,work/'scripts'/name);inputs.append({'path':str(f),'sha256':sha(f)})
 for name in ['STIXGeneral.ttf','LICENSE_STIX']:
  f=b/'fonts'/name;shutil.copyfile(f,work/'reports/fonts'/name);inputs.append({'path':str(f),'sha256':sha(f)})
 source=b/'paper/ANALYTIC_ENGINE_EXPOSITION.md';shutil.copyfile(source,work/'paper'/source.name);inputs.append({'path':str(source),'sha256':sha(source)})
 accepted=b/'paper/ANALYTIC_ENGINE_EXPOSITION_24CASE_REVIEW_DRAFT_V2.html';text=accepted.read_text();title=re.search(r'<title>(.*?)</title>',text,re.S);need(title is not None,'accepted paper title');import html;title=html.unescape(title[1]);raw=out/'paper/ANALYTIC_ENGINE_EXPOSITION.raw.html';final=out/'paper/ANALYTIC_ENGINE_EXPOSITION.html'
 bootstrap='import runpy,sys; n=int(sys.argv[1]); sys.path[:0]=sys.argv[2:2+n]; script=sys.argv[2+n]; sys.argv=sys.argv[2+n:]; runpy.run_path(script,run_name="__main__")'
 argv=[sys.executable,'-I','-B','-S','-c',bootstrap,str(len(wheels)),*wheels,str(work/'scripts/build_final_report.py'),'--input',str(work/'paper'/source.name),'--output',str(raw),'--title',title]
 rows=[run(argv,out/'render-command')];rows.append(run([sys.executable,'-I','-B','-S',str(work/'scripts/embed_offline_math_font.py'),'--input',str(raw),'--output',str(final),'--receipt',str(out/'FONT_RECEIPT.json')],out/'font-command'))
 actual=final.read_text();math=lambda s:re.findall(r'<math\b[^>]*>.*?</math>',s,re.S);article=lambda s:re.search(r'<article>(.*?)</article>',s,re.S)[1]
 need(math(actual)==math(text),'every accepted MathML byte identical after clean regeneration');need(article(actual)==article(text),'complete source-correct mathematical exposition article identical');need(len(math(actual))==138,'complete current exposition138MathML expressions')
 receipt={'status':'PASS_CLEAN_OFFLINE_PAPER_REGENERATION_ALL_ARTICLE_AND_MATHML_BYTES_IDENTICAL','inputs':inputs,'wheels':deps['wheels'],'commands':rows,'accepted':{'path':str(accepted),'sha256':sha(accepted)},'output':{'path':str(final),'sha256':sha(final)},'MathML_expressions':len(math(actual)),'same_mathematical_article':True,'source_footer_relative_href_may_differ_with_layout':True,'no_network_model_Lean_compiler_or_numerical_ANT_execution':True,'Python_site_packages_disabled':True,'dependency_code_loaded_only_from_exact_two_wheels':True,'controller_sha256':sha(Path(__file__))}
 with (out/'RECEIPT.json').open('x')as f:json.dump(receipt,f,indent=2);f.write('\n')
 print(json.dumps({'status':receipt['status'],'receipt_sha256':sha(out/'RECEIPT.json')},sort_keys=True))
if __name__=='__main__':main()
