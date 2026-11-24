#!/usr/bin/env python3
"""Bounded real-CLI association controls; never invoke a historical proof reader."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=HERE/'controls-v2'
ORIGIN=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-octic-20261123/network')
DELIVERED=Path('/data/ivy-rh-octic-20261123/final-archive-verification-v1/extracted/publication')
RUN=Path('/data/ivy-rh-octic-20261123/ramanujan/ieantn-count-consumer-v2')
C=Path('Solutions/RHOcticPush.v1/ramanujan/count-feasibility')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 need(not OUT.exists(),'fresh control namespace');OUT.mkdir();(OUT/'fixtures').mkdir()
 pins=json.loads((HERE/'SOURCE_ASSOCIATION_PINS.json').read_text())
 closure=json.loads((ORIGIN/C/'ieantn-consumer/SOURCE_CLOSURE.json').read_text())
 paths={x['path'] for x in pins['sources']+pins['metadata']}|{x['source'] for x in closure['files']}
 watched={str(ORIGIN/p):sha(ORIGIN/p) for p in paths}
 watched.update({x['path']:sha(Path(x['path'])) for x in pins['receipts']})
 watched.update({x['actual_execution_provider']:sha(Path(x['actual_execution_provider'])) for x in pins['bank_engines']})
 base=OUT/'fixtures/base';base.mkdir()
 for rel in paths:
  p=base/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(DELIVERED/rel,p)
 rows=[]
 for i,mode in enumerate([[],['-O'],['-OO']]):
  prefix=[sys.executable,'-B',*mode,str(HERE/'source_association.py')]
  args=['--accepted-source-root',str(ORIGIN),'--delivered-root',str(DELIVERED),'--ieantn-run',str(RUN)]
  def run(name,cmd,positive,gate):
   label=name+'-O'+str(i);cp=subprocess.run(cmd,capture_output=True)
   stdout=OUT/(label+'.stdout');stderr=OUT/(label+'.stderr');stdout.write_bytes(cp.stdout);stderr.write_bytes(cp.stderr)
   need((cp.returncode==0)==positive,'unexpected decision '+label)
   need(gate in (cp.stdout+cp.stderr).decode(),'specific expected gate '+label)
   rows.append(dict(label=label,command=cmd,returncode=cp.returncode,expected_positive=positive,expected_gate=gate,
       stdout_sha256=sha(stdout),stderr_sha256=sha(stderr)))
  receipt=OUT/('positive-O'+str(i)+'.json')
  run('actual-association',prefix+args+['--out',str(receipt)],True,'metadata only')
  run('actual-receipt-readback',prefix+args+['--check-receipt',str(receipt)],True,'unchanged source association receipt')
  wrong=OUT/'fixtures/empty-origin';wrong.mkdir(exist_ok=True)
  wrongargs=args.copy();wrongargs[1]=str(wrong)
  run('wrong-origin',prefix+wrongargs+['--out',str(OUT/('reject-origin-O'+str(i)+'.json'))],False,'exact accepted original source root')
  run('wrong-context',prefix+args+['--context',str(base/pins['context_relative']),'--out',str(OUT/('reject-context-O'+str(i)+'.json'))],False,'exact original-ROOT context path')
  cases=[('changed-code',pins['sources'][0]['path'],'change','validator byte association'),
      ('missing-code',str(C/'cold-foundation/source_basis.py'),'missing','regular nonsymlink file'),
      ('changed-delivered-engine',pins['bank_engines'][0]['published_path'],'change','validator byte association'),
      ('missing-delivered-engine',pins['bank_engines'][1]['published_path'],'missing','regular nonsymlink file'),
      ('changed-metadata',str(C/'ieantn-consumer/RESOURCE_POLICY.json'),'change','declared metadata/pinned reader byte association'),
      ('changed-declared-Lean',closure['files'][1]['source'],'change','declared consumer source byte association'),
      ('symlink-provider',pins['sources'][0]['path'],'symlink','regular nonsymlink file')]
  for name,rel,mutation,gate in cases:
   fixture=OUT/'fixtures'/(name+'-O'+str(i));shutil.copytree(base,fixture)
   p=fixture/rel
   if mutation=='change':p.write_bytes(p.read_bytes()+b'\n# owned mutation only\n')
   elif mutation=='missing':p.unlink()
   else:p.unlink();p.symlink_to(ORIGIN/rel)
   aa=args.copy();aa[3]=str(fixture)
   run(name,prefix+aa+['--out',str(OUT/(name+'-reject-O'+str(i)+'.json'))],False,gate)
  for name,data,gate in [('duplicate-receipt',b'{"status":"a","status":"b"}','duplicate JSON field'),
      ('nonfinite-receipt',b'{"status":NaN}','nonfinite JSON'),
      ('overflow-float-receipt',b'{"status":1e999}','nonfinite JSON float')]:
   p=OUT/(name+'-O'+str(i)+'.json');p.write_bytes(data)
   run(name,prefix+args+['--check-receipt',str(p)],False,gate)
  p=OUT/('forged-receipt-O'+str(i)+'.json');data=json.loads(receipt.read_text());data['source_owned_python_files']=10;save(p,data)
  run('forged-receipt',prefix+args+['--check-receipt',str(p)],False,'exact source-association receipt')
  run('existing-output',prefix+args+['--out',str(receipt)],False,'fresh association receipt path')
  run('malformed-flag',prefix+args+['--accepted-source-roo','bad','--out',str(OUT/('badflag-O'+str(i)+'.json'))],False,'unrecognized arguments')
  run('missing-flags',prefix+['--out',str(OUT/('missingflags-O'+str(i)+'.json'))],False,'the following arguments are required')
  run('finalizer-help',[sys.executable,'-B',*mode,str(HERE/'finalize_bundle.py'),'--help'],True,'--accepted-source-root')
  run('finalizer-required-origin',[sys.executable,'-B',*mode,str(HERE/'finalize_bundle.py')],False,'--accepted-source-root')
 after={p:sha(Path(p)) for p in watched};need(after==watched,'original source/bank metadata/engine preservation')
 save(OUT/'PRESERVATION.json',dict(status='PASS_ALL_EXPLICIT_ORIGINAL_INPUTS_UNCHANGED',files=len(watched),before=watched,after=after,
     scope='Original selected source/metadata, locked receipts and two bank-engine files only. No whole-bank object census or proof validator invoked.'))
 save(OUT/'RESULT.json',dict(status='PASS_ACTUAL_ASSOCIATION_CLI_CONTROLS_ALL_THREE_PYTHON_MODES',rows=rows,
     decisions=len(rows),helper_sha256=sha(HERE/'source_association.py'),pins_sha256=sha(HERE/'SOURCE_ASSOCIATION_PINS.json'),
     finalizer_sha256=sha(HERE/'finalize_bundle.py'),parent_validators_invoked=False,compilers_invoked=False,
     bank_or_original_mutations=False,scope='Metadata source-association CLI positives and owned delivered-fixture negatives; no mathematical or PV acceptance.'))
 print('PASS',len(rows),'actual CLI decisions; no parent proof reader/compiler')
if __name__=='__main__':main()
