"""Run real added C++ moment entries; numerical observations are not proof acceptance.

Preserve oldmain/helpers, compile real objects, inspect actual linker/CRT/main wrapping,
then execute both changed moment workloads. The source/loop/ANT proofs are separate.
"""
from pathlib import Path
import argparse,hashlib,json,math,os,re,shlex,subprocess,time
B=Path(__file__).resolve().parent
EXPECTED_LD_SHA='58937fc20c21e147883b4fdaa0fc7438a8e8f2bb886cfcaa4896100ca91139e7'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key '+k);d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON '+x)
 def floating(s):
  v=float(s);need(math.isfinite(v),'overflowJSON');return v
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def atomic(p,a):
 t=p.with_suffix('.pending');t.write_text(json.dumps(a,indent=2)+'\n');os.replace(t,p)
def source_inputs():
 p=strict(B/'SOURCE_PLAN_V1.json');prior=B.parent/'moment-program-v1';oldplan=strict(prior/'SOURCE_PLAN_V2.json')
 need(p['prior_program_plan_sha256']==sha(prior/'SOURCE_PLAN_V2.json'),'pinned unchanged prior program plan')
 need(len(p['variants'])==2 and[x['name']for x in p['variants']]==['mass','first_moment'],'two exact high-only variants')
 need({x.name:sha(x)for x in(prior/'source/base').iterdir()if x.is_file()}==oldplan['original_files'],'unchanged original full physical source')
 for row in p['variants']:
  need(sha(B/row['translation_unit'])==row['translation_unit_sha256']and sha(B/row['entry'])==row['entry_sha256'],'exact new source '+row['name'])
  previous=prior/'source'/(row['name']+'-entry.cpp');need(sha(previous)==row['prior_entry_sha256'],'exact old entry preserved')
  text=previous.read_text();need(text.count(row['change']['old'])==1,'one local update difference')
  need(text.replace(row['change']['old'],row['change']['new'])==(B/row['entry']).read_text(),'precise additive high-only change')
 return dict(compiler_sha256=oldplan['compiler_sha256'],compiler_flags=oldplan['compiler_flags'],variants=[dict(name=x['name'],translation_unit=Path(x['translation_unit']).name,entry_source_sha256=x['entry_sha256'],translation_unit_sha256=x['translation_unit_sha256'])for x in p['variants']])

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--compiler',type=Path);ap.add_argument('--baseline',type=Path);ap.add_argument('--check-inputs-only',action='store_true');ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();plan=source_inputs();out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh external output');
 if a.check_inputs_only:
  out.mkdir(parents=True);atomic(out/'RECEIPT.json',dict(status='HIGH_ONLY_C_SOURCE_IDENTITIES_ONLY_NOT_EXECUTION',source_plan_sha256=sha(B/'SOURCE_PLAN_V1.json')));return
 need(a.compiler is not None and a.baseline is not None,'compiler and regenerated baseline required');need(sha(a.compiler)==plan['compiler_sha256'],'pinned clang');baseline=a.baseline.read_bytes();need(len(baseline)==98432 and hashlib.sha256(baseline).hexdigest()=='9eed8900f85288d3c6890688417b53d9ecde40ccd837bf34e8993afba2ccc22e','exact retained old run');out.mkdir(parents=True);records=[];start=time.monotonic()
 def execute(directory,name,command,binary_output=False):
  stdout=directory/(name+'.stdout');stderr=directory/(name+'.stderr');timing=directory/(name+'.time');began=time.monotonic()
  with stdout.open('wb')as so,stderr.open('wb')as se:q=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],stdout=so,stderr=se)
  row=dict(name=name,command=command,exit_code=q.returncode,seconds=time.monotonic()-began,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),time_sha256=sha(timing));need(q.returncode==0,'failed '+name);return row,stdout
 try:
  for variant in plan['variants']:
   name=variant['name'];d=out/name;d.mkdir();source=B/'source'/variant['translation_unit'];obj=d/'program.o';binary=d/'program';linkmap=d/'program.map';commands=[]
   compilecmd=[str(a.compiler),*plan['compiler_flags'],'-c',str(source),'-o',str(obj)];r,_=execute(d,'compile',compilecmd);commands.append(r)
   linkcmd=[str(a.compiler),'-fuse-ld=/usr/bin/ld',str(obj),'-Wl,--wrap=main','-Wl,-Map='+str(linkmap),'-o',str(binary)]
   r,trace=execute(d,'link-driver-trace',[str(a.compiler),'-###',*linkcmd[1:]]);commands.append(r);lines=(d/'link-driver-trace.stderr').read_text().splitlines();links=[]
   for line in lines:
    try:parts=shlex.split(line)
    except ValueError:continue
    if parts and Path(parts[0]).name in{'ld','ld.bfd','ld.lld','x86_64-linux-gnu-ld','x86_64-linux-gnu-ld.bfd'}:links.append(parts)
   need(len(links)==1,'one actual linker selected');selected=links[0];ld=Path(selected[0]);need(ld.is_file()and sha(ld)==EXPECTED_LD_SHA and '--wrap=main'in selected and str(obj)in selected,'pinned selected linker and own linked object')
   crt=[];mainrefs=[]
   for path in selected[1:]:
    p=Path(path)
    if p.is_file()and p.suffix=='.o'and p.resolve()!=obj.resolve():
     crt.append(dict(path=str(p),sha256=sha(p)))
     r,text=execute(d,'CRT-'+str(len(crt))+'-symbols',['readelf','-Ws',str(p)]);commands.append(r)
     if re.search(r'\bUND\s+main\s*$',text.read_text(),re.M):mainrefs.append(str(p))
   need(crt and mainrefs,'actual selected CRT has undefinedmainreference')
   r,_=execute(d,'link',linkcmd);commands.append(r)
   r,symbols=execute(d,'object-symbols',['nm','-g','--defined-only',str(obj)]);commands.append(r);st=symbols.read_text()
   need(all(re.search(r'^\s*[0-9a-fA-F]+\s+T\s+'+re.escape(x)+r'\s*$',st,re.M)for x in['main','__wrap_main']),'oldmain plus actual C-linkagewrapper retained in own linked object')
   r,sym=execute(d,'binary-symbols',['nm','-an',str(binary)]);commands.append(r);addresses={}
   for line in sym.read_text().splitlines():
    m=re.fullmatch(r'([0-9a-fA-F]+)\s+[Tt]\s+(main|__wrap_main|_start)',line.strip())
    if m:addresses[m.group(2)]=int(m.group(1),16)
   need(set(addresses)=={'main','__wrap_main','_start'}and len(set(addresses.values()))==3,'distinct original/wrapper/start binary symbols')
   r,entry=execute(d,'actual-start-disassembly',['objdump','-d','--disassemble=_start',str(binary)]);commands.append(r);entrytext=entry.read_text();need('<__wrap_main>'in entrytext and '<main>'not in entrytext,'actual CRT startup selects wrapperaddress')
   need(linkmap.is_file()and'__wrap_main'in linkmap.read_text()and str(obj)in linkmap.read_text(),'actual linked ownobject/wrapper map')
   r,_=execute(d,'linker-version',[str(ld),'--version']);commands.append(r)
   r,raw=execute(d,'run',[str(binary)],True);commands.append(r);data=raw.read_bytes();need(len(data)==98432 and data[:98304]==baseline[:98304],'actual entire unchanged768 C/D rowprefix');oldsource=B.parent/'moment-program-v1/source'/(name+'.cpp');oldbinary=d/'old-v1-program';r,_=execute(d,'old-v1-compile',[str(a.compiler),*plan['compiler_flags'],str(oldsource),'-fuse-ld=/usr/bin/ld','-Wl,--wrap=main','-o',str(oldbinary)]);commands.append(r);r,priorraw=execute(d,'old-v1-run',[str(oldbinary)]);commands.append(r);need(data==priorraw.read_bytes(),'byte-for-byte full observable output equivalence to freshly regenerated old interval-update entry');tail=data[-128:];lo=int.from_bytes(tail[:64],'little');hi=int.from_bytes(tail[64:],'little');need(lo<=hi,'observed intervalorder only; notsoundnessproof')
   row=dict(name=name,status='RAW_NEW_CPP_ENTRY_BUILD_LINK_AND_OUTPUT_ASSOCIATION_ONLY',commands=commands,source_sha256=sha(source),entry_source_sha256=variant['entry_source_sha256'],object_sha256=sha(obj),binary_sha256=sha(binary),linkmap_sha256=sha(linkmap),selected_linker=str(ld),selected_linker_sha256=sha(ld),selected_CRT=crt,actual_CRT_undefined_main_references=mainrefs,binary_symbols=addresses,output_bytes=len(data),output_sha256=sha(raw),unchanged_point_rows_sha256=hashlib.sha256(data[:98304]).hexdigest(),physical_total_low=str(lo),physical_total_high=str(hi),physical_total_denominator=str(1<<128),prior_entry_output_sha256=sha(priorraw),full_observable_output_equal=True,source_first_PV=False,numerical_enclosure_verified=False,qualification='Real changed workload execution and exact source/build/object/linker/CRT/wrapper/output association. No application source execution correctness, numerical interval soundness or ANT refinement follows from this raw observation. All originalsource functions retained; pinned GNUldwrap+CRT contract explicit.')
   atomic(d/'RECEIPT.json',row);records.append(row);atomic(out/'PROGRESS.json',dict(status='PARTIAL_RAW_ASSOCIATION_ONLY',completed=len(records)))
  source_inputs();atomic(out/'RECEIPT.json',dict(status='PASS_TWO_HIGH_ONLY_MOMENT_ENTRY_ASSOCIATIONS_AND_COMPLETE_BYTE_EQUIVALENCE_NOT_FORMAL_PROOF',seconds=time.monotonic()-start,records=records,source_plan_sha256=sha(B/'SOURCE_PLAN_V1.json'),reproducer_sha256=sha(Path(__file__)),baseline_output_sha256=sha(a.baseline),source_first_PV=False,numerical_enclosures_verified=False,qualification='Own C/C++ source, linker/CRT entry routing, native outputs and provenance only. Kernel and source-loop/mathematical consumer proofs remain required. Binaries/objects retained for this unfinished experiment; no unrelated cleanup.'))
 except Exception as exc:atomic(out/'FAILURE.json',dict(status='RAW_ASSOCIATION_FAILED_PRESERVED',error=str(exc),seconds=time.monotonic()-start,records=records));raise
if __name__=='__main__':main()
