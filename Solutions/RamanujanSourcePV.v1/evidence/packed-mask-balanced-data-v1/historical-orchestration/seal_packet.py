from pathlib import Path
import hashlib,json,re,shutil,sys,zipfile,datetime
W=Path('/ryu/hyunsik/playground/independence/codex/ivy');S=W/'ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1';D=Path('/data/ivy-ramanujan-source-pv-20261119/packed-mask-balanced-data-scout');P=S/'evidence/packed-mask-balanced-data-v1'
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def copy(a,b):
 b.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a,b)
need(not P.exists(),'fresh packet');P.mkdir(parents=True)
# A source-only application closure, no accepted baseline mask proof import.
seen={};pending=['RamanujanPV.PackedSievePrimitiveBits','RamanujanPV.PackedMaskEncodingCodec']
while pending:
 mod=pending.pop()
 if mod in seen:continue
 f=S/Path(*mod.split('.')).with_suffix('.lean')
 if not f.exists():continue
 seen[mod]=str(f);copy(f,P/'source'/f.relative_to(S))
 for line in f.read_text().splitlines():
  m=re.match(r'^\s*(?:public\s+|private\s+)?import\s+(.+)',line)
  if m:pending.extend(m[1].split())
 for name in re.findall(r'include_str\s+"([^"]+)"',f.read_text()):
  payload=(f.parent/name).resolve();copy(payload,P/'source'/payload.relative_to(S))
copy(S/'BUILD_CONTEXT.json',P/'BUILD_CONTEXT.json')
for name in ['generate_balanced_mask_data.py','reproduce_profiled_closure.py','rebuild_qrh_closure.py','compile_lean.py','compile_lean_context.py']:
 copy(S/'scripts'/name,P/'scripts'/name)
copy(S/'evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean',P/'inputs/accepted-mask-input.lean.txt')
copy(D/'run_fixed_encodings.py',P/'historical-orchestration/run_fixed_encodings.py')
for f in(D/'launch-v1').iterdir():
 if f.is_file():copy(f,P/'historical-orchestration/launch-v1'/f.name)
for f in(D/'source-versions').rglob('*'):
 if f.is_file():copy(f,P/'historical-generators'/f.relative_to(D/'source-versions'))
copy(D/'REGENERATION_ALL_MODES.json',P/'REGENERATION_ALL_MODES.json')
for label in ['normal','O','OO']:
 copy(D/f'regeneration-{label}-v3/PROPOSAL.json',P/f'regeneration/{label}/PROPOSAL.json')
expected=json.loads((D/'regeneration-normal-v3/PROPOSAL.json').read_text())
(P/'REGENERATED_SOURCE_HASHES.json').write_text(json.dumps({r['module']:r['sha256']for r in expected['records']},indent=2)+'\n')
# Keep successful and unsuccessful proof receipts, snapshots and native GNU time.
receipts=sorted(D.glob('**/RUN.json'))+[S/'audit/RamanujanPV.PackedMaskEncodingCodec/1/RUN.json'];rows=[]
for f in receipts:
 o=json.loads(f.read_text());rel=f.relative_to(D)if f.is_relative_to(D)else Path('generic-codec')/f.relative_to(S/'audit')
 dest=P/'attempts'/rel.parent
 for file in f.parent.iterdir():
  if file.is_file():copy(file,dest/(file.name+'.txt'if file.name=='source.lean'and o['returncode']!=0 else file.name))
 need(sha(f.parent/'source.lean')==o['source_sha256'],'source snapshot')
 for name,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(f.parent/name)==o[key],'receipt log')
 obj=Path(o['command'][-1]);size=None
 if o['returncode']==0:
  need(obj.is_file()and sha(obj)==o['object_sha256'],'object readback');size=obj.stat().st_size
 text=(f.parent/'rusage.txt').read_text();rss=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',text)[1])*1024
 axioms=[]
 for name,values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(f.parent/'stdout').read_text()):
  vals=[x.strip()for x in values.split(',')if x.strip()];need(set(vals)<={'propext','Classical.choice','Quot.sound'},'standard axioms');axioms.append(dict(declaration=name,axioms=vals))
 rows.append(dict(module=o['module'],attempt=str(dest.relative_to(P)),status=o['status'],source_sha256=o['source_sha256'],object_sha256=o.get('object_sha256'),object_bytes=size,seconds=o['elapsed_seconds'],max_rss_bytes=rss,per_run_AS_bytes=o['memory_limit_bytes'],source_bytes=(f.parent/'source.lean').stat().st_size,axioms=axioms,returncode=o['returncode']))
(P/'ATTEMPTS.json').write_text(json.dumps(rows,indent=2)+'\n')
summary=dict(status='KERNEL_DATA_ENCODING_AND_STANDALONE_MASK_EQUALITIES_ACCEPTED',created=datetime.datetime.now(datetime.timezone.utc).isoformat(),fixed_input=dict(lo=38358837684,count=1000000,chunk_widths=[256,1024,4096],seed=None,packed_little_endian_sha256=expected['baseline_packed_sha256']),recommended_module='RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.Data',recommended_data_seconds=4.535180659964681,recommended_data_olean_bytes=194288,recommended_standalone_unchanged_program_seconds=110.7340306006372,baseline_data_seconds=26.12657928466797,previous_full_mask_proof_seconds=133.06625039875507,annotation_only_variant=True,attempts=len(rows),failed_attempts=sum(r['returncode']!=0for r in rows),source_only_generic_closure_modules=len(seen),source_regeneration_all_modes=True,fresh_complete_replay_of_this_packet=False,no_new_ANT_result=True,no_new_C_PV=True,no_native_decide=True,scope='Same million-bit mask DATA and exact kernel equalities only; standalone provider imports neither baseline DATA nor the previous accepted mask proof. Incremental observed timings are not a global speedup claim. Calibration requires separate one-time baseline DATA compilation. All failed attempts preserved; no OOM was observed in this scout.')
(P/'RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(P);print(json.dumps(summary,indent=2))
