#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,re,sys
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1')
D=Path('/data/ivy-ramanujan-source-pv-20261119')
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def reject(x):raise ValueError('nonfinite metadata')
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=reject)
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--audit-dir',type=Path,default=S/'audit/RamanujanPV.PackedSieveResultIndependentAudit/1');a=p.parse_args();ctx=read(S/'BUILD_CONTEXT.json')
def check_receipt(q):
 q=Path(q);d=read(q);need(d['status']=='COMPILED'and d['returncode']==0,'actual successful compilation');src=Path(d['source']);obj=Path(d['command'][-1]);need(sha(src)==d['source_sha256'],'exact source identity');need(sha(q.parent/'source.lean')==d['source_sha256'],'actual compiler snapshot');need(sha(obj)==d['object_sha256'],'current object identity');need(d['compiler_sha256']==sha(ctx['compiler'])==ctx['compiler_sha256'],'pinned compiler');need(d['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'generic context')
 for f,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(q.parent/f)==d[key],'actual log identity')
 return dict(receipt=str(q),receipt_sha256=sha(q),source=str(src),source_sha256=sha(src),object=str(obj),object_sha256=sha(obj),seconds=d['elapsed_seconds'],stdout_sha256=d['stdout_sha256'])
base=S/'evidence/packed-sieve-million-independent-v1';need(sha(base/'PACKET.json')=='a0817fcdd42ca71b32899d90d5e8909d627bf516b7c88940010c765aebb9c2a1','preserved main independent packet');need(sha(base/'RESULT.json')=='6719f8a94888594ff39f457d4de145339d8bfffc6df01c70ab65c11050e7374c','preserved main independent result')
audit=check_receipt(a.audit_dir/'RUN.json');root=check_receipt(S/'audit/RamanujanPV.PackedSieveResult/1/RUN.json');text=(a.audit_dir/'stdout').read_text();root_source=Path(root['source']).read_text();need(re.findall(r'(?m)^import (.+)$',root_source)==['RamanujanPV.PackedSieveMillion'],'exact one-module incremental joint source')
required=['RamanujanPV.PackedSieveResult.actual_source_bindings','RamanujanPV.QuotientCSourceV2.actual_source_checked','RamanujanPV.QuotientDriverSource.actual_source_checked','RamanujanPV.SegmentCheckerSource.actual_source_checked','RamanujanPV.FiniteExpSource.actual_source_checked','RamanujanPV.FiniteLogSource.actual_source_checked','RamanujanPV.FiniteCellSource.actual_source_checked','RamanujanPV.PackedSieveQueries.row_source_counts','RamanujanPV.PackedSieveProvider.source_bound_provider','RamanujanPV.SegmentCFunction.positive_output_sound','RamanujanPV.QuotientCFunction.linked_function_refines','RamanujanPV.PackedSievePrimitiveMaskMillion.packed_bits','RamanujanPV.PackedSievePrimitiveQWindow.packed_bits','RamanujanPV.FiniteCellProtected.positive_implies_strict','IEANTN.primeCounting'];facts=[]
for suffix,math in [('source_linked_uniform_gap','uniform_gap'),('source_linked_real_interval','first_1000001_real_interval')]:
 name='RamanujanPV.PackedSieveResult.'+suffix
 m=re.search(r'^PACKED_JOINT_COMPLETE_CLOSURE '+re.escape(name)+r' (\d+)$',text,re.M);need(m is not None,'full separate joint closure report')
 ax=re.search(r'^PACKED_JOINT_COMPLETE_AXIOMS '+re.escape(name)+r' \[([^]]+)\]',text,re.M);need(ax is not None,'mandatory actual axiom closure');axes=[x.strip()for x in ax.group(1).split(',')];need(set(axes)=={'propext','Classical.choice','Quot.sound'},'complete standard-only axiom universe')
 paths=re.findall(r'^PACKED_JOINT_ACTUAL_PATH '+re.escape(name)+r': (.+)$',text,re.M);need(len(paths)==16 and {x.split(' -> ')[-1]for x in paths}==set(required+['RamanujanPV.PackedSieveMillion.'+math]),'all16 independently compulsory actual paths')
 facts.append(dict(root=name,complete_proof_type_constants=int(m.group(1)),axioms=axes,required_paths=paths,external_theorem_inputs=0))
# Exact aliases make the checked optimized counter AST identical to the AST used in execution.
alias=(S/'RamanujanPV/QuotientCSource.lean').read_text();need('abbrev countFunction := QuotientCSourceV2.countFunction'in alias and 'abbrev sqrtFunction := QuotientCSourceV2.sqrtFunction'in alias,'same executed source AST aliases')
cfiles={}
for name in ['verified_quotient_count.c','verified_quotient_driver_n0.c','verified_segment_checker.c','verified_finite_exp.c','verified_finite_log.c','verified_finite_cell.c']:
 q=S/'c'/name;need(q.is_file(),'actual frozen C source');cfiles[name]=dict(path=str(q),bytes=q.stat().st_size,sha256=sha(q))
result=dict(status='PASS_SEPARATE_INDEPENDENT_JOINT_SOURCE_BINDINGS_AND_PACKED_REAL_THEOREMS',python_optimization=sys.flags.optimize,pure_root_packet_sha256=sha(base/'PACKET.json'),root_receipt=root,independent_audit=audit,joint_root_closures=facts,actual_C_sources=cfiles,incremental_import_count=549,import_count_method='Prior actual548 application import census plus this exact one-module wrapper, whose sole import is PackedSieveMillion. The audit helper adds no application import.',all_six_source_bindings_required=True,same_executed_counter_AST=True,trust_boundary='Mathematical function execution and exact same-AST source binding; no physical packed loader/caller/process association or new native packed implementation. Global finite counts remain outside this completed window.')
need(not a.out.exists(),'fresh output');a.out.parent.mkdir(parents=True,exist_ok=True);temp=a.out.with_suffix(a.out.suffix+'.tmp');temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(a.out);print(json.dumps(dict(status=result['status'],python_optimization=sys.flags.optimize,closures=[x['complete_proof_type_constants']for x in facts])))
