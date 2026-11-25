#!/usr/bin/env python3
"""Actual pre-browser CLI rejection cases in normal/-O/-OO; explicit guards."""
import argparse,copy,hashlib,json,os,re,subprocess,sys,tempfile
from pathlib import Path

def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def publish(p,x):
    need(not p.exists(),'Fresh receipt required');fd,n=tempfile.mkstemp(dir=p.parent,prefix='.acceptance-');q=Path(n)
    try:
        with os.fdopen(fd,'w') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(q,p)
    finally:q.unlink()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--html',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();need(not a.output.exists(),'Fresh controls required');a.output.mkdir(parents=True);script=Path(__file__).with_name('check_report_browser.py');text=a.html.read_text();metadata=json.loads(a.html.with_name('REPORT_BUILD.json').read_text());rows=[]
    cases=[('existing_output','Fresh output directory required'),('viewport','Invalid viewport syntax'),('bad_hash','HTML metadata hash differs'),('script','Static report contains script'),('no_math','Insufficient MathML source population'),('math_count','MathML metadata population differs'),('duplicate_json','Duplicate JSON key'),('nan_json','Non-finite JSON constant'),('release_no_repo','Source-link gate requires --repository'),('font_bytes','Embedded math font bytes differ'),('bool_population','Invalid MathML population metadata'),('low_contrast_visual','header source-pin contrast below4.5'),('page_overflow_visual','page-level horizontal overflow')]
    for opt in [[],['-O'],['-OO']]:
        mode=opt[0][1:] if opt else 'normal'
        for name,guard in cases:
            d=a.output/(mode+'-'+name);d.mkdir();html=d/'report.html';meta=d/'REPORT_BUILD.json';out=d/'browser-output';html.write_text(text);m=copy.deepcopy(metadata);flags=[]
            if name=='existing_output':out.mkdir()
            if name=='viewport':flags=['--viewports','broken']
            if name=='bad_hash':m['html_sha256']='0'*64
            if name=='script':html.write_text(text.replace('</body>','<script></script></body>'))
            if name=='no_math':html.write_text(re.sub(r'<math\b.*?</math>','<span>omitted negative fixture</span>',text,flags=re.S));m['rendered_occurrences']=0
            if name=='math_count':m['rendered_occurrences']+=1
            if name=='release_no_repo':flags=['--verify-source-links']
            if name=='font_bytes':html.write_text(re.sub(r'src:url\(data:font/ttf;base64,[A-Za-z0-9+/=]+\)','src:url(data:font/ttf;base64,d3Jvbmc=)',text))
            if name=='bool_population':m['rendered_occurrences']=True
            if name=='low_contrast_visual':
                html.write_text(text.replace('</style>','header .fine{color:rgb(76,91,112)!important}</style>',1));flags=['--viewports','320x740']
            if name=='page_overflow_visual':
                html.write_text(text.replace('</style>','body{min-width:500px!important}</style>',1));flags=['--viewports','320x740']
            if name!='bad_hash':m['html_sha256']=sha(html)
            raw=json.dumps(m)
            if name=='duplicate_json':raw='{"html_sha256":"'+m['html_sha256']+'",'+raw[1:]
            if name=='nan_json':raw='{"unaccepted":NaN,'+raw[1:]
            meta.write_text(raw+'\n');cmd=[sys.executable,*opt,str(script),'--html',str(html),'--metadata',str(meta),'--output',str(out),*flags];r=subprocess.run(cmd,capture_output=True);(d/'stdout').write_bytes(r.stdout);(d/'stderr').write_bytes(r.stderr);need(r.returncode!=0 and guard in r.stderr.decode(),'Wrong actual CLI rejection '+mode+':'+name);need(not (out/'RESULT.json').exists(),'Rejected input emitted acceptance');rows.append(dict(mode=mode,name=name,command=cmd,returncode=r.returncode,required_guard=guard,html_sha256=sha(html),metadata_sha256=sha(meta),stdout_sha256=sha(d/'stdout'),stderr_sha256=sha(d/'stderr')))
    x=dict(status='PASS_ALL_39_ACTUAL_CLI_AND_BROWSER_VISUAL_REJECTION_CONTROLS',cases=rows,checker_sha256=sha(script),controller_sha256=sha(Path(__file__)),claim='Actual input/guard and rendered-visual rejection only; positive actual browser results have separate receipts.');publish(a.output/'RESULT.json',x);print(json.dumps(dict(status=x['status'],cases=len(rows))))
if __name__=='__main__':main()
