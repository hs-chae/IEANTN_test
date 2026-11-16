"""Deterministically regenerate untrusted C point/statistic/prefix proposals.
All mathematical validity is independently established by the later Lean kernel.
"""
from pathlib import Path
import argparse,hashlib,json,math,os,re,subprocess,time
B=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(text):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicateJSON');d[k]=v
  return d
 def bad(x):raise ValueError('nonfiniteJSON')
 def floating(x):
  y=float(x);need(math.isfinite(y),'overflowJSON');return y
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def strict(p):return parse(p.read_text())
def atomic(p,v):
 q=p.with_suffix('.pending');q.write_text(json.dumps(v,indent=2)+'\n');os.replace(q,p)
def inputs():
 lock=strict(B/'NATIVE_INPUTS.json')
 for r in lock['sources']:
  p=B/r['path'];need(p.is_file()and not p.is_symlink()and sha(p)==r['sha256']and p.stat().st_size==r['bytes'],'native physical input '+r['path'])
 need(lock['cells']==768 and lock['precision_bits']==128 and lock['word_bits']==512,'fixed parameters')
 return lock
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--compiler',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args();lock=inputs();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh external numericaloutput');out.mkdir(parents=True);start=time.monotonic();records=[]
 if a.check_inputs_only:atomic(out/'RECEIPT.json',dict(status='NUMERICAL_SOURCE_IDENTITIES_ONLY_NO_EXECUTION',source_inputs=len(lock['sources']),source_first_PV=False));return
 need(a.compiler is not None and sha(a.compiler)==lock['compiler_sha256'],'pinned actual clang');need(sha(Path('/usr/bin/ld').resolve())==lock['ld_sha256'],'selected GNUld reproducibility pin')
 def execute(d,name,cmd):
  so=d/(name+'.stdout');se=d/(name+'.stderr');tm=d/(name+'.time');t=time.monotonic()
  with so.open('wb')as f,se.open('wb')as g:q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],stdout=f,stderr=g)
  need(q.returncode==0,'numerical step '+name);return dict(name=name,command=cmd,exit_code=q.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(so),stderr_sha256=sha(se),time_sha256=sha(tm)),so
 try:
  baseline=None
  for kind in ['height','mass','first_moment']:
   d=out/kind;d.mkdir();unit=B/('research/moment-program-v1/source/base/height_bundle.cpp'if kind=='height'else'research/moment-hi-program-v1/source/'+kind+'.cpp');binary=d/'program';flags=[]if kind=='height'else['-Wl,--wrap=main'];cmd=[str(a.compiler),*lock['compiler_flags'],str(unit),'-fuse-ld=/usr/bin/ld',*flags,'-o',str(binary)];cr,_=execute(d,'compile',cmd);rr,raw=execute(d,'run',[str(binary)]);data=raw.read_bytes();expected=lock['baseline_output_sha256']if kind=='height'else lock['expected_outputs'][kind];need(len(data)==98432 and sha(raw)==expected,'exact deterministic raw '+kind)
   if kind=='height':baseline=data
   else:need(data[:98304]==baseline[:98304],'same768point rows')
   footer=d/'accepted-observed-footer.bin';footer.write_bytes(data[-128:]);record=dict(kind=kind,source_sha256=sha(unit),commands=[cr,rr],output_sha256=sha(raw),output_bytes=len(data),footer_sha256=sha(footer),binary_sha256=sha(binary),proposer_correctness_is_not_assumed=True)
   if kind=='height':
    proposed=[(int.from_bytes(data[128*i:128*i+64],'little'),int.from_bytes(data[128*i+64:128*i+128],'little'))for i in range(768)];locked=[]
    for block in range(96):
     text=(B/'source/SourceMomentWordsV1'/f'Block{block:02d}.lean').read_text();part=text.split('def words : List (Int × Int) := ',1)[1].split('\ntheorem checked',1)[0];values=[(int(x),int(y))for x,y in re.findall(r'\((\d+),(\d+)\)',part)];need(len(values)==8,'eight locked modelwords');locked+=values
    need(proposed==locked,'all768numericalpointpairs regenerated')
   else:
    entry=B/'research/moment-hi-program-v1/source'/(kind+'-entry.cpp');text=entry.read_text();needle='emitU((D.hi));\n';need(text.count(needle)==1,'one prefix instrumentation site');instrumented=text.replace(needle,needle+'emitI(total);\n');src=d/'prefix-proposal.cpp';src.write_text('#include "'+str(B/'research/moment-program-v1/source/base/height_bundle.cpp')+'"\n'+instrumented);proposal=d/'prefix-proposal';pcmd=[str(a.compiler),*lock['compiler_flags'],str(src),'-fuse-ld=/usr/bin/ld','-Wl,--wrap=main','-o',str(proposal)];pcr,_=execute(d,'prefix-compile',pcmd);prr,pr=execute(d,'prefix-run',[str(proposal)]);payload=pr.read_bytes();need(len(payload)==768*256+128 and payload[-128:]==data[-128:],'full prefix framing/footer');pointrows=b''.join(payload[256*i:256*i+128]for i in range(768));need(pointrows==data[:98304],'unmodified point data');prefixes=[(0,0)]+[(int.from_bytes(payload[256*i+128:256*i+192],'little'),int.from_bytes(payload[256*i+192:256*i+256],'little'))for i in range(768)];source=(B/'source/SourceMomentSumsV1/Data.lean').read_text();part=source.split('def '+kind+' : List ProofBox := ',1)[1].split('\n',1)[0];locked=[(int(x),int(y))for x,y in re.findall(r'⟨(\d+),(\d+)⟩',part)];need(len(locked)==769 and prefixes==locked,'all769exact locked numerical prefixes '+kind);record.update(prefix_commands=[pcr,prr],prefix_output_sha256=sha(pr),prefix_binary_sha256=sha(proposal),prefix_source_sha256=sha(src),prefix_data_count=769)
   records.append(record);atomic(out/'PROGRESS.json',dict(completed=len(records),records=records))
  inputs();atomic(out/'RECEIPT.json',dict(status='PASS_ALL_DETERMINISTIC_C_PROPOSALS_REGENERATED_AND_SOURCE_WORD_DATA_MATCHED',seconds=time.monotonic()-start,records=records,native_input_lock_sha256=sha(B/'NATIVE_INPUTS.json'),reproducer_sha256=sha(Path(__file__)),compiler_sha256=sha(a.compiler),source_first_PV=False,mathematical_acceptance=False,qualification='Untrusted deterministic proposals only; later exactkernel build independently proves all768pointwords andbothprefixsums/mathconsumers. No native output is a theorem premise.'))
 except Exception as ex:atomic(out/'FAILURE.json',dict(status='FAILED_NUMERICAL_REGENERATION_NOT_ACCEPTED',error=str(ex),records=records));raise
if __name__=='__main__':main()
