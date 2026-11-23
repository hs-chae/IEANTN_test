#!/usr/bin/env python3
"""Attach the strict-endpoint theorem to the completed fresh117-source replay.

All117 source/object associations and the executed replay controller are checked;
no historical application object bank is used on this final118-source chain.
"""
from pathlib import Path
import argparse,os,re,resource,subprocess,time
from reproduce import read,save,need,sha,audit,COMPILER_SHA
B=Path(__file__).resolve().parent;N=B.parents[2];OLD=N/'Solutions/RHContinuation.v1'
def check_base(base):
 r=read(base/'RESULT.json');need(r['status']=='PASS_COMPLETE_SAME_SOURCE111_PLUS_FOUR_CLOSED_OCTIC_CONTRACTS','base final status')
 need(r['no_prebuilt_application_objects']is True and r['original_modules']==111 and r['new_modules']==6,'base scope')
 need(r['compiler_sha256']==COMPILER_SHA and r['controller_sha256']==sha(base/'reproduce.executed.py'),'base executed compiler/controller')
 need(r['manifest_sha256']==sha(base/'OCTIC_MANIFEST.executed.json')and r['BUILD_sha256']==sha(base/'BUILD.json'),'base manifest/build association')
 m=read(base/'OCTIC_MANIFEST.executed.json');need(m['original_manifest_sha256']==sha(OLD/'integration/SOURCE_CLOSURE.json'),'original source manifest')
 original=read(OLD/'integration/SOURCE_CLOSURE.json')['modules'];expected=[x['module']for x in original]+[x['module']for x in m['new_modules']]
 rows=read(base/'BUILD.json')['modules'];need(len(rows)==117 and [x['module']for x in rows]==expected,'base exact module membership')
 need({str(p.relative_to(base/'objects'))for p in(base/'objects').rglob('*')if p.is_file()}=={x['module'].replace('.','/')+'.olean'for x in rows},'base exact object membership')
 for x in rows:
  rel=x['module'].replace('.','/');need(x['returncode']==0 and sha(base/'source'/(rel+'.lean'))==x['source_sha256']and sha(base/'objects'/(rel+'.olean'))==x['object_sha256'],'base source/object identity')
 return r,rows

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--base-run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();base=a.base_run.resolve();out=a.out.resolve();need(not out.exists(),'fresh output')
 r,rows=check_base(base);binding=sha(base/'BUILD.json');ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',OLD/'scripts/GENERIC_CONTEXT.json')));need(sha(ctx['compiler'])==COMPILER_SHA,'compiler pin')
 src0=B/'OcticStrict.lean';expected=read(B/'STRICT_MANIFEST.json');need(sha(src0)==expected['sha256'],'strict source pin')
 out.mkdir();src=out/'OcticStrict.lean';src.write_bytes(src0.read_bytes());obj=out/'OcticStrict.olean';env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out),str(base/'objects'),*ctx['generic_libraries']]);cmd=[ctx['compiler'],'--root='+str(out),'-j8','-o',str(obj),str(src)];st=time.monotonic();run=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=out,env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
 (out/'stdout').write_text(run.stdout);(out/'stderr').write_text(run.stderr);need(run.returncode==0,'strict source compile failed');roots=audit(run.stdout,expected['audits']);need(sha(src)==sha(src0)==expected['sha256'],'strict source drift');check_base(base);need(binding==sha(base/'BUILD.json'),'base mutated during append')
 row={'module':'OcticStrict','source_sha256':sha(src),'object_sha256':sha(obj),'returncode':0,'command':cmd,'seconds':time.monotonic()-st,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr).group(1)),'axiom_audits':roots}
 save(out/'RESULT.json',{'status':'PASS_COMPLETE118_SOURCE_CHAIN_WITH_STRICT_ENDPOINT_COUNTS','scope':'Fresh111historical+6new fullreplay followed by strictsource compilation against that samefreshbank; not a second cold118run.','base_run':str(base),'base_result_sha256':sha(base/'RESULT.json'),'base_BUILD_sha256':binding,'base_source_modules':117,'source_modules_total':118,'no_historical_application_objects':True,'compiler_sha256':COMPILER_SHA,'controller_sha256':sha(__file__),'strict_manifest_sha256':sha(B/'STRICT_MANIFEST.json'),'executed_compile_seconds':r['seconds']+row['seconds'],'max_child_RSS_KiB':max(r['peak_child_RSS_KiB'],row['peak_RSS_KiB']),'base_final_owned_bytes':r['final_owned_bytes'],'append_final_owned_bytes':sum(p.stat().st_size for p in out.rglob('*')if p.is_file()),'module':row,'remaining_contracts':['EvenKernel.ExplicitFormula','EvenKernel.ZeroEstimate'],'source_first_PV':False,'OOM':'all118 accepted compiler jobs returned0; kernel OOM counter not independently attributed'})
 print('PASS_COMPLETE118_SOURCE_CHAIN_WITH_STRICT_ENDPOINT_COUNTS',flush=True)
if __name__=='__main__':main()
