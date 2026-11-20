from pathlib import Path
import hashlib,json,re,shutil
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');D=Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-independent-audit-v1');O=S/'evidence/packed-sieve-independent-v1';O.mkdir(exist_ok=False)
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
records=[]
def audit(receipt):
 receipt=Path(receipt);r=json.loads(receipt.read_text());folder=receipt.parent;source=Path(r['source']);obj=Path(r['command'][-1]);need(r['status']=='COMPILED'and r['returncode']==0 and r['source_unchanged_during_compile']is True and sha(source)==r['source_sha256']==sha(folder/'source.lean')and sha(obj)==r['object_sha256'],'actualcurrentproofassociation '+r['module'])
 for f,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/f)==r[k],'actualreceiptpayload')
 target=O/'accepted'/r['module'];target.mkdir(parents=True)
 for f in ['RUN.json','source.lean','stdout','stderr','rusage.txt']:shutil.copyfile(folder/f,target/f)
 text=(folder/'stdout').read_text();axes={name:[a.strip()for a in body.split(',')if a.strip()]for name,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
 for name in re.findall(r"'([^']+)' does not depend on any axioms",text):axes[name]=[]
 need(all(set(xs)<={'propext','Classical.choice','Quot.sound'}for xs in axes.values()),'standardactualaxesonly')
 row=dict(module=r['module'],source=str(source),source_sha256=sha(source),object_sha256=sha(obj),receipt=str(receipt),receipt_sha256=sha(receipt),seconds=r['elapsed_seconds'],axioms=axes);records.append(row);return row
readback=json.loads((D/'SOURCE_READBACK.json').read_text())
for item in readback['records']:audit(item['receipt'])
for n,a in [('PackedSieveSlices',1),('PackedSievePrimitiveBits',1),('PackedSieveInstances',4),('PackedSieveProviderIndependentAudit',2)]:audit(S/'audit'/('RamanujanPV.'+n)/str(a)/'RUN.json')
for n in ['PackedSieveByteControl1000','PackedSieveByteBlock0000']:audit(Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-byte-profile-v1/audit')/('RamanujanPV.'+n)/'1/RUN.json')
q=audit(Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-primitive-v1/audit/RamanujanPV.PackedSievePrimitiveQWindow/1/RUN.json'))
a=S/'audit/RamanujanPV.PackedSieveProviderIndependentAudit/2';log=(a/'stdout').read_text();counts={n:int(v)for n,v in re.findall(r'PACKED_COMPLETE_CONSTANT_CLOSURE (\S+) (\d+)',log)};need(counts=={'RamanujanPV.PackedSieveProvider.source_bound_provider':10404,'RamanujanPV.PackedSieveByteTail.byteCountFast_ceil_width':5353,'RamanujanPV.PackedSieveSlices.checkSlices_from_zero':5363},'actualcompletegenericclosures')
csources=[]
for n in ['verified_segment_checker.c','verified_quotient_count.c','verified_quotient_driver_n0.c']:
 f=S/'c'/n;target=O/'c'/n;target.parent.mkdir(exist_ok=True);shutil.copyfile(f,target);csources.append(dict(file='c/'+n,sha256=sha(f)))
for n in ['SOURCE_READBACK.json','NUMERIC_CONTROLS_READBACK.json','Q_NATIVE_EVERY_BIT_READBACK.json','check_q_mask.py']:shutil.copyfile(D/n,O/n)
result=dict(status='PASS_BOUNDED_GENERIC_PACKED_SOURCE_PROVIDER_AND_ACCEPTED_SCOPED_NUMERIC_READBACK',scope=dict(frozen_generic_modules=11,additional_science=['PackedSieveSlices','PackedSievePrimitiveBits','PackedSieveInstances'],accepted_numeric_modules=['PackedSieveByteControl1000','PackedSieveByteBlock0000','PackedSievePrimitiveQWindow'],independent_compiled_audit='PackedSieveProviderIndependentAudit2',excluded='NoP-millionnumericalproviderorwholepackedmillionANTconsumeracceptedbythisaudit.'),roots=counts,all_actual_axioms=['propext','Classical.choice','Quot.sound'],native_execution_axioms=False,source_correspondences=csources,source_path=['geometricmasktestBit','least-prime-factorclassificationwithnoprimetableinput','256-entrybytetableallkernelproved','exactpartial-bytezeropadding','constructedcanonicalstatic-arraylayout/ownership','modeledclaimheapwordsfromprovedpackedbits','actualfullsegmentedCguard/init/divisor/check/countRun','positive_output_soundviafullsourceexecutiondeterminism','prefixcountplusSOURCE_VERIFIEDanchor','QuotientCountRealizationactualquotientCmodeledexecution','SourceExecutioninterfacefortheexistingIEANTNcellconsumer'],explicit_premises=['base:SourceExecution(lo−1,baseValue)','2≤lo','0<count','lo+count−1≤2e12','count≤sourcecapacity1500000'],not_assumed=['prime/compositetable','arbitraryflagclassification','Ownedinitialheap','scratchallocation','inputEnvbindings','desiredpositiveoutput','arbitraryNatprime-countequality'],accepted_numeric_scope=dict(kernel_controls=[dict(lo=38358837684,count=1000,increment=32),dict(lo=38358837684,count=65536,increment=2664)],actual_source_execution_and_count_instances=[dict(N=38358838683,pi=1644673264),dict(N=38358903219,pi=1644675896)],Q_kernel_all_bits=dict(lo=14111427771,count=367880,increment=15972,source_sha256=q['source_sha256'],receipt_sha256=q['receipt_sha256']),P_million_not_accepted_in_this_scope=True),trust_boundaries=['Thepackedproducer,bytecounterandslicecheckerarenewLeankernelmathematics,NOTsource-firstPVofanewnativepackedCimplementation.','ActualCsourcePVreusesUNCHANGEDrpc_check_segment;theindependentproofalsoseparatelychecksbytebindingofrpc_quotient_count.','inputHeapconstructsmodeledclaimwordsbyFunction.updateovertheprovedstatic-arraylayout;NOactualCloader/storeexecutionfromzeroarraystotheseclaimwordsisprovedhere.','TheanchorSourceExecutionisexplicitandmustbeclosedbytheapplication;itcannotbechosenasanunverifiedcountoracle.','Aphysicalcall/loading/build/process/stdoutassociationremainsoutsidegenericfunctioncontract;genericpinnedcompiler/runtime/ABI/hardwarecontractsremainrelevanttoanyphysicaluse.','SourceExecutionisthenetworkcountinterface;newpackedmillionrealANTconsumerrequiresseparategroundP/Q/queryandfinalconsumerproofs.','Slicesprovesbit-prefixcounts;integerprime-counttransportstillrequiresin-rangequeryandsource-provider/anchorapplicability.'],primitive_identity='foralllo/count,primitiveBits=maskXOR(maskANDcompositeMask)=oldprimeBits;allfourBooleanbitcasesproved;nosource/Coremathematicalinputchanged.',supplemental_Q_readback='IndependentordinaryPythonEratosthenesmatchedEVERYQbitand15972countin0.0285s;nativeobservationonly,notformalPV.',findings='No blocking mathematical/source-path defect found in the exact audited universe. Boundaries above are explicit scope limits, not repaired implementation claims.',records=records)
(O/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
text='''Independent packed-sieve/source-provider audit: PASS in the bounded scope.

The frozen11 modules and their current accepted source/snapshot/object/log hashes
match. A separately compiled48GiB CPU16 audit checks all10,404 constants in
source_bound_provider's proof/type closure,5,353 in the proved byte accumulator,
and5,363 in the disjoint-slice checker. Only the standard three logical axioms
occur; no native execution axiom, unproved SWAR routine or ground numeric result
is needed by the generic provider.

The source chain is genuine for the UNCHANGED C segmented checker: all input
flags follow from the proved packed sieve, the scratch flags are initialized by
actual source stores, every necessary divisor is visited, the complete actual
C body returns count+1, and positive_output_sound checks every completed modeled
run through source determinism. The same AST renders the exact C bytes. The
result becomes the existing quotient-count SourceExecution consumed by IEANTN.
The quotient C byte binding is independently checked separately.

Important explicit boundary: the provider takes a SOURCE-VERIFIED anchor count,
not an arbitrary prime-count equality. It constructs a modeled heap containing
packed-derived claim words over the proved source static-array allocation.
The Function.update loading of claim words is mathematical state construction,
not a proved C loader/store program. No native packed-bitset implementation,
physical caller/loader/process/stdout association or full packed million ANT
consumer is certified by these generic modules.

The AND/XOR primitiveBits identity is exact for all inputs and preserves the
entire old bitset. It is kernel representation optimization, not verification
of new native C packing code. Byte population table entries, partial-byte
padding, accumulator equivalence and slice-prefix arithmetic are proved.
Slices alone gives bit counts; source-query bounds and the verified anchor are
still required for actual prime counts.

Accepted scoped numerical readbacks:
- lo38358837684,width1000:32 primes (kernel,40.159s).
- same lo,width65536:2664 primes (kernel,68.078s).
- SourceExecution/Nat prime counts at38358838683=1644673264 and
  38358903219=1644675896 are completed in PackedSieveInstances4.
- Qlo14111427771,width367880:every original prime bit is sealed; exact byte
  count15972 is kernel-proved (80.656s). An independent ordinary Python sieve
  additionally matched every Q bit; this is supplemental native evidence.
No P-million numerical success or full new million consumer is claimed here.

Exact compiler receipts, source bytes, C files, hashes and all remaining trust
boundaries are in RESULT.json and accepted/. The original generic56-module cold
replay completed separately; its result is not a ground numeric million proof.
'''
(O/'REVIEW.txt').write_text(text);shutil.copyfile(__file__,O/'seal.py');files=[]
for f in sorted(O.rglob('*')):
 if f.is_file():files.append(dict(path=str(f.relative_to(O)),sha256=sha(f),bytes=f.stat().st_size))
p=dict(status='SEALED_BOUNDED_PACKED_SIEVE_INDEPENDENT_AUDIT',payload=files,files=len(files),bytes=sum(v['bytes']for v in files));(O/'PACKET.json').write_text(json.dumps(p,indent=2)+'\n');print(json.dumps(dict(result_sha256=sha(O/'RESULT.json'),packet_sha256=sha(O/'PACKET.json'),files=len(files),bytes=p['bytes'])))
