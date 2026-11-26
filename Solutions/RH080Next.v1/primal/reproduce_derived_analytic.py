#!/usr/bin/env python3
"""Fresh source-only kernel verification for additive affine analytic lemmas."""
import argparse,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--root',choices=['AffineDerivativeBounds','AffineCellInterpolation'],default='AffineDerivativeBounds');a=ap.parse_args();need(not a.out.exists(),'Fresh directory required');a.out.mkdir(parents=True);here=Path(__file__).resolve().parent;repo=here.parents[2];c=json.loads(a.context.read_text());controller=sha(Path(__file__));need(sha(Path(c['compiler']))==c['compiler_sha256'],'Compiler differs');paths=c['generic_lean_path'].split(':');need(len(paths)==len(c['generic_dependencies']),'Generic library population differs')
 for path,dep in zip(paths,c['generic_dependencies']):
  p=Path(path).parents[3];need(p.name==dep['name'],'Generic order differs');need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==dep['revision'],'Generic revision differs');need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=p,text=True),'Generic tracked source dirty')
 roots=[here,repo/'Solutions/RH080Next.v1/explicit'];seen=set();rows=[]
 def generic(m):return m.startswith(('Mathlib','Lean.','Std.','Init.'))or m in ['Lean','Std','Init']
 def visit(m):
  if generic(m)or m in seen:return
  seen.add(m);src=next((r/(m.replace('.','/')+'.lean')for r in roots if(r/(m.replace('.','/')+'.lean')).exists()),None);need(src is not None,'Missing source '+m);imports=[]
  for line in src.read_text().splitlines():
   if line.startswith('import '):imports+=line[7:].split('--',1)[0].split()
  for x in imports:visit(x)
  rows.append(dict(module=m,origin=str(src),source_sha256=sha(src)))
 visit(a.root);source=a.out/'source';objects=a.out/'objects';logs=a.out/'logs'
 for p in [source,objects,logs]:p.mkdir()
 for row in rows:
  p=source/(row['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(row['origin']).read_bytes())
 (a.out/'PLAN.json').write_text(json.dumps(dict(modules=rows,compiler_sha256=c['compiler_sha256'],generic_dependencies=c['generic_dependencies'],application_object_fallback=False),indent=2)+'\n');env=dict(os.environ,LEAN_PATH=str(objects.resolve())+':'+c['generic_lean_path']);allowed={'propext','Classical.choice','Quot.sound'};results=[];start=time.monotonic()
 for row in rows:
  m=row['module'];src=source/(m.replace('.','/')+'.lean');obj=objects/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);cmd=['/usr/bin/time','-v',c['compiler'],'-j1','--root='+str(source.resolve()),'-o',str(obj.resolve()),str(src.resolve())];t=time.monotonic();p=subprocess.run(cmd,env=env,text=True,capture_output=True);(logs/(m+'.stdout')).write_text(p.stdout);(logs/(m+'.stderr')).write_text(p.stderr);need(p.returncode==0,'Lean rejected '+m);audits=re.findall(r'depends on axioms: \[([^\]]*)\]',p.stdout);none=len(re.findall(r'does not depend on any axioms',p.stdout));need(len(audits)+none==src.read_text().count('#print axioms'),'Incomplete axiom audit '+m);need(all({x.strip()for x in s.split(',')if x.strip()}<=allowed for s in audits),'Nonstandard axiom '+m);need(sha(src)==row['source_sha256']==sha(Path(row['origin'])),'Changed source '+m);peak=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.stderr);need(len(peak)==1,'Missing resource metric');results.append(dict(module=m,seconds=time.monotonic()-t,peak_RSS_kib=int(peak[0]),command=cmd,source_sha256=sha(src),object_sha256=sha(obj),audited_roots=len(audits)+none));print(m,'PASS',flush=True)
 need(sha(Path(__file__))==controller,'Controller changed');result=dict(status='PASS_COMPLETE_COLD_AFFINE_ANALYTIC_LEMMA_KERNEL_STD3',root=a.root,modules=len(rows),source_first_PV=False,application_object_fallback=False,seconds=time.monotonic()-start,max_process_RSS_kib=max(r['peak_RSS_kib']for r in results),disk_bytes=sum(p.stat().st_size for p in a.out.rglob('*')if p.is_file()),compiler_sha256=c['compiler_sha256'],controller_sha256=controller,commands=results);temp=a.out/'RESULT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.out/'RESULT.json');temp.unlink();print(result['status'])
if __name__=='__main__':main()
