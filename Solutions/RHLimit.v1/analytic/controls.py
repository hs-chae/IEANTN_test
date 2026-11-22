#!/usr/bin/env python3
"""All-mode actual CLI and parser/axiom-audit rejection controls; no assert acceptance."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,subprocess,sys
B=Path(__file__).resolve().parent

def need(b,m):
 if not b:raise ValueError(m)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls required');out.mkdir(parents=True)
 rows=[]
 for flags in ([],['-O'],['-OO']):
  mode='normal'if not flags else flags[0][1:];owned=out/mode;owned.mkdir()
  def cli(name,args,expected,env=None):
   dest=Path(args[args.index('--out')+1]);receipt=dest/'RESULT.json';before=receipt.read_bytes()if receipt.exists()else None
   cmd=[sys.executable,*flags,str(B/'reproduce.py'),*args];r=subprocess.run(cmd,text=True,capture_output=True,env=env)
   (owned/(name+'.stdout')).write_text(r.stdout);(owned/(name+'.stderr')).write_text(r.stderr)
   need((r.returncode==0)==expected,'unexpected acceptance:'+mode+':'+name)
   if not expected:
    after=receipt.read_bytes()if receipt.exists()else None;need(before==after,'negative route published/changed receipt')
   rows.append({'mode':mode,'test':name,'expected_acceptance':expected,'returncode':r.returncode,'command':cmd})
  cli('preflight',['--out',str(owned/'check'),'--check'],True)
  cli('full-bound-base-two-proof-replay',['--out',str(owned/'accepted'),'--base-run',str(a.base_run)],True)
  cli('existing-output',['--out',str(owned/'accepted'),'--check'],False)
  for name,raw in [('duplicate-context','{"compiler_sha256":"a","compiler_sha256":"b"}'),('nonfinite-context','{"bad":1e999}')]:
   ctx=owned/(name+'.json');ctx.write_text(raw);env=os.environ.copy();env['IEANTN_GENERIC_CONTEXT']=str(ctx)
   cli(name,['--out',str(owned/(name+'-out')),'--check'],False,env)
  bad=owned/'incomplete-base';bad.mkdir();(bad/'RESULT.json').write_text('{"status":"RUNNING"}')
  cli('incomplete-base',['--out',str(owned/'bad-base-out'),'--base-run',str(bad)],False)
  cli('unknown-option',['--out',str(owned/'unknown-out'),'--che'],False)
  check=owned/'audit-check.py';check.write_text('''import importlib.util,sys\ns=importlib.util.spec_from_file_location('v',sys.argv[1]);v=importlib.util.module_from_spec(s);s.loader.exec_module(v)\nfor text,names in [("'x' depends on axioms: [sorryAx]",['x']),("'x' depends on axioms: [propext]\\n'x' depends on axioms: [propext]",['x']),("'x' depends on axioms: [propext]",['y'])]:\n try:v.audit(text,names)\n except ValueError:continue\n raise RuntimeError('audit accepted malformed evidence')\nprint('PASS_AUDIT_REJECTIONS')\n''')
  cmd=[sys.executable,*flags,str(check),str(B/'reproduce.py')];r=subprocess.run(cmd,text=True,capture_output=True);need(r.returncode==0 and 'PASS_AUDIT_REJECTIONS'in r.stdout,'axiom guard failure');rows.append({'mode':mode,'test':'axiom-audit-rejections','returncode':r.returncode,'command':cmd})
 receipt={'controller_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'validator_sha256':hashlib.sha256((B/'reproduce.py').read_bytes()).hexdigest(),'status':'PASS_ALL_MODE_CONTROLS','rows':rows,'scope':'Actual fresh/check/bound-base/negative CLIs in normal,-O,-OO plus isolated audit rejection controls; fresh46-source route has separate cold48-v1 receipt.'};q=out/'.RESULT.pending';q.write_text(json.dumps(receipt,indent=2)+'\n');q.replace(out/'RESULT.json');print(receipt['status'])
if __name__=='__main__':main()
