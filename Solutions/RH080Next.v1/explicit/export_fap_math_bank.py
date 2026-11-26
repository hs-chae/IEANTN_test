#!/usr/bin/env python3
"""Format-only export of fully validated original Fap source-cold proof objects.
No compiler or numerical run is performed, and no historical status changes.
The normalized records retain every original source/receipt/log/hash lineage,
including the interruption/resume and all generated FFT forest sources.
"""
from __future__ import annotations
import argparse,json,os,shutil,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;S=HERE.parent;R=S.parents[1]
sys.path.insert(0,str(S/'primal/finite'))
from reproduce_finite_nodes import context,validate_math
from reproduce_fap_fft_math import load,need,publish,sha

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--math-base',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--validate-only',action='store_true');a=ap.parse_args();need(not os.path.lexists(a.run),'fresh format-export directory required');began=time.monotonic();c=context(a.context,R);base=a.math_base.resolve(strict=True);bp,fp,objects=validate_math(base,c,a.context);forest=Path(bp['forest_base']);inherited={x['module']:x for x in bp.get('inherited_modules',[])};inventory={x['path']:x for x in objects};rows=[];lineage=[]
    for x in fp['sources']:
      if not x['file'].endswith('.lean'):continue
      n=x['file'][:-5];snapshot=forest/'sources'/x['file'];repo=S/'dual'/x['file'];need(not repo.is_file() or sha(repo)==x['sha256'],'current tracked forest module differs');origin=repo if repo.is_file() else snapshot;rp=forest/(n+'.COMPILED.json');cr=load(rp);need(cr['module']==n and cr['returncode']==0,'invalid forest compiler receipt');objectPath=n+'.olean';need(objectPath in inventory,'missing forest object');normalized=dict(cr,exitcode=cr['returncode'],object_sha256=inventory[objectPath]['sha256'],receipt_kind='FORMAT_EXPORT_OF_EXISTING_SOURCE_COLD_COMPILATION_NO_NEW_EXECUTION',original_compiler_receipt=str(rp),original_compiler_receipt_sha256=sha(rp),original_source_sha256=x['sha256'],original_log_directory=str(forest));rows.append(dict(module=n,origin=str(origin),snapshot=str(snapshot),source_sha256=x['sha256'],generated_source=(origin==snapshot),regeneration='Solutions/RH080Next.v1/primal/reproduce_fap_fft_math.py; originalN17/stage17/42-source forest unchanged'));lineage.append((n,normalized))
    for x in bp['additional_sources']:
      n=x['module'];rp=Path(inherited[n]['receipt']) if n in inherited else base/(n.replace('.','_')+'.COMPILED.json');cr=load(rp);need(cr['module']==n and cr['exitcode']==0,'invalid mathematical compiler receipt');objectPath=n.replace('.','/')+'.olean';need(objectPath in inventory and inventory[objectPath]['sha256']==cr['object_sha256'],'mathematical object identity differs');normalized=dict(cr,receipt_kind='FORMAT_EXPORT_OF_EXISTING_SOURCE_COLD_COMPILATION_NO_NEW_EXECUTION',original_compiler_receipt=str(rp),original_compiler_receipt_sha256=sha(rp),original_log_directory=str(rp.parent/'logs'));rows.append(dict(module=n,origin=x['origin'],snapshot=x['snapshot'],source_sha256=x['source_sha256'],generated_source=False));lineage.append((n,normalized))
    need(len(rows)==184 and len({r['module'] for r in rows})==184,'fixed184 source identities required')
    for x in rows:need(sha(Path(x['origin']))==sha(Path(x['snapshot']))==x['source_sha256'],'source changed during format validation')
    if a.validate_only:
      a.run.mkdir(parents=True);publish(a.run/'RESULT.json',dict(status='PASS_FAP_SOURCE_COLD_LINEAGE_VALIDATION_ONLY_NO_EXPORT',sources=184,forest_sources=42,additional_sources=142,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,original_math_result_sha256=sha(base/'RESULT.json'),original_forest_result_sha256=sha(forest/'RESULT.json'),controller_sha256=sha(Path(__file__)),python_optimization=sys.flags.optimize,seconds=time.monotonic()-began));print('PASS full184-source Fap lineage validation only; no export or new proof');return
    a.run.mkdir(parents=True);bank=a.run/'objects';bank.mkdir()
    for obj in objects:
      src=base/'objects'/obj['path'];dst=bank/obj['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);need(sha(dst)==obj['sha256'],'copied object changed')
    for n,receipt in lineage:publish(a.run/(n+'.COMPILED.json'),receipt)
    for x in rows:need(sha(Path(x['origin']))==sha(Path(x['snapshot']))==x['source_sha256'],'source changed during format export')
    (a.run/'controller.executed.py').write_bytes(Path(__file__).read_bytes());publish(a.run/'PLAN.json',dict(status='FORMAT_ONLY_EXPORT_OF_VALIDATED_SOURCE_COLD_FAP_MATH_NO_COMPILATION',source_rows=rows,context_sha256=sha(a.context),original_math_base=str(base),original_math_result_sha256=sha(base/'RESULT.json'),original_math_plan_sha256=sha(base/'PLAN.json'),original_forest=str(forest),original_forest_result_sha256=sha(forest/'RESULT.json'),original_forest_plan_sha256=sha(forest/'PLAN.json'),original_object_inventory_sha256=sha(base/'OBJECTS.json'),controller_sha256=sha(Path(__file__)),application_object_fallback=False,source_cold=False,source_first_PV_complete=False,generated_sources_regenerate_not_published=True));publish(a.run/'RESULT.json',dict(status='PASS_FORMAT_EXPORT_VALIDATED_SOURCE_COLD_FAP_MATH_NO_NEW_COMPILATION',sources=184,objects=len(objects),forest_sources=42,additional_mathematical_sources=142,source_cold_lineage_preserved=True,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,source_numerical_status='KERNEL_ONLY_NOT_C_FFT_PV',seconds=time.monotonic()-began,python_optimization=sys.flags.optimize,logical_disk_bytes=sum(x.stat().st_size for x in a.run.rglob('*') if x.is_file())));print('PASS format-only export:184 exact source/receipt-associated Fap mathematical objects; no new run or PV claim')
if __name__=='__main__':main()
