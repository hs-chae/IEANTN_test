"""Actual offline report CLI controls; no mathematical or model execution."""
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys
A=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 for name in ['data','font','exposition','comparison-html','source-map','out']:p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--public-root',type=Path);a=p.parse_args();need(not a.out.exists(),'fresh actual CLI controls');a.out.mkdir()
 data=json.loads(a.data.read_bytes());smap=json.loads(a.source_map.read_bytes());fixtures=a.out/'fixtures';fixtures.mkdir();cases=[('complete',a.data,a.source_map,a.comparison_html,True)]
 bad=copy.deepcopy(data);bad['all48_family_summaries']=bad['all48_family_summaries'][:-1];f=fixtures/'missing-family.json';f.write_text(json.dumps(bad));cases.append(('missing-family',f,a.source_map,a.comparison_html,False))
 bad=copy.deepcopy(data);bad['cases_with_actual_clean_relocated_full_reproduction']=23;f=fixtures/'unperformed-case.json';f.write_text(json.dumps(bad));cases.append(('unperformed-case',f,a.source_map,a.comparison_html,False))
 for label,raw in [('duplicate','{"stages":null,'+a.data.read_text()[1:]),('nonfinite','{"overflow":1e9999,'+a.data.read_text()[1:])]:
  f=fixtures/(label+'.json');f.write_text(raw);cases.append((label,f,a.source_map,a.comparison_html,False))
 import re
 used=next(h.partition('#')[0] for h in re.findall(r'href=[\"\']([^\"\']+)',a.comparison_html.read_text()) if h.startswith('/'))
 bad=copy.deepcopy(smap);need(used in bad['files'],'actual first source in map');bad['files'][used]['sha256']='0'*64;f=fixtures/'changed-source-map.json';f.write_text(json.dumps(bad));cases.append(('changed-source',a.data,f,a.comparison_html,False))
 f=fixtures/'script.html';f.write_text(a.comparison_html.read_text()+'<script>throw 0</script>');cases.append(('browser-script',a.data,a.source_map,f,False));rows=[];produced=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  for label,dp,mp,cp,ok in cases:
   out=a.out/(mode+'-'+label);out.mkdir();argv=[sys.executable,'-I','-B',*flags,str(A/'render_main_report_complete_v4.py'),'--data',str(dp.resolve()),'--font',str(a.font.resolve()),'--exposition',str(a.exposition.resolve()),'--comparison-html',str(cp.resolve()),'--source-map',str(mp.resolve()),'--out',str((out/'report.html').resolve())]
   if a.public_root is not None:argv+=['--public-root',str(a.public_root.resolve())]
   x=subprocess.run(argv,capture_output=True);(out/'stdout').write_bytes(x.stdout);(out/'stderr').write_bytes(x.stderr);need((x.returncode==0)==ok,'actual renderer '+mode+' '+label)
   if ok:produced.append((sha(out/'report.html'),sha(out/'report.md')))
   else:need(not (out/'report.html').exists() and not (out/'report.md').exists(),'no success artifacts after rejected inputs')
   rows.append({'mode':mode,'case':label,'argv':argv,'returncode':x.returncode,'expected_success':ok,'stdout_sha256':sha(out/'stdout'),'stderr_sha256':sha(out/'stderr')})
 need(len(set(produced))==1,'normal/O/OO full human HTML and Markdown identical')
 result={'status':'PASS_ACTUAL_COMPLETE_RENDERER_V4_NORMAL_O_OO_AND_REJECTION_CONTROLS','source':{'path':str(A/'render_main_report_complete_v4.py'),'sha256':sha(A/'render_main_report_complete_v4.py')},'controller':{'path':str(Path(__file__)),'sha256':sha(Path(__file__))},'inputs':[{ 'path':str(q.resolve()),'sha256':sha(q)} for q in [a.data,a.font,a.exposition,a.comparison_html,a.source_map]],'rows':rows,'mode_HTML_Markdown_byte_identical':True,'models_compilers_mathematical_numerics':0,'browser_visual_test_claimed':False}
 with (a.out/'RESULT.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({'status':result['status'],'actual_CLIs':len(rows),'receipt_sha256':sha(a.out/'RESULT.json')},sort_keys=True))
if __name__=='__main__':main()
