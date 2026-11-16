"""Deterministic raw C regeneration. Does not claim source-first PV."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,sys
P=Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise RuntimeError(message)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(pairs):
    result={}
    for key,value in pairs:
        need(key not in result,'duplicate JSON key '+key)
        result[key]=value
    return result
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--compiler',type=Path);a=ap.parse_args()
    manifest_path=P/'HEIGHT_REGEN_MANIFEST_V1.json';m=json.loads(manifest_path.read_text(),object_pairs_hook=unique);expected={'height-point-constants-v1':'c/height_point_constants_v1.cpp','height-point-h-v1':'c/height_point_h_v1.cpp','height-point-q-v1':'c/height_point_q_v1.cpp','height-point-768-full-v1':'c/height_point_768_full_v1.cpp','height-point-polybudget-v1':'c/height_point_polybudget_v1.cpp'}
    need(len(m['programs'])==5 and {r['name']:r['source']for r in m['programs']}==expected,'exact five source routes required')
    need(set(m['includes'])=={'c/height_point_common_v1.inc','c/basis_fp128_height_v2.cpp'},'exact application include population required')
    out=a.out.resolve()
    need(P not in out.parents and out != P,'Output must be outside the numerical source capsule')
    need(not out.exists(),'Fresh output required');out.mkdir(parents=True)
    cc=a.compiler or Path(m['compiler_default']);need(sha(cc)==m['compiler_sha256'],'Compiler hash differs from pinned toolchain')
    for q,h in m['includes'].items():need(sha(P/q)==h,'Include drift '+q)
    version=subprocess.run([str(cc),'--version'],capture_output=True,text=True,check=True).stdout
    records=[];beg=time.monotonic()
    for r in m['programs']:
        src=P/r['source'];need(sha(src)==r['source_sha256'],'Source drift '+r['source']);case=out/r['name'];case.mkdir();exe=case/'program';blob=case/'output.bin'
        cmd=[str(cc),*m['compiler_flags'],str(src),'-o',str(exe)];t=time.monotonic();q=subprocess.run(cmd,capture_output=True,text=True);(case/'compiler.stderr').write_text(q.stderr);need(q.returncode==0,'Compile failure '+r['name'])
        with blob.open('wb')as stream, (case/'run.stderr').open('wb')as stderr:
            run=subprocess.run(['/usr/bin/time','-v',str(exe)],stdout=stream,stderr=stderr)
        need(run.returncode==0,'Run failure '+r['name']);digest=sha(blob);need(digest==r['output_sha256'],'Output mismatch '+r['name']);need(sha(src)==r['source_sha256'],'Source changed during run')
        row={'name':r['name'],'compile_command':cmd,'run_command':['/usr/bin/time','-v',str(exe)],'source_sha256':sha(src),'binary_sha256':sha(exe),'output_sha256':digest,'output_bytes':blob.stat().st_size,'seconds':time.monotonic()-t,'status':'EXACT_RAW_REGENERATION_PASS','source_first_PV':False}
        records.append(row);(case/'RECEIPT.json').write_text(json.dumps(row,indent=2)+'\n')
        # The checked output and receipts are small and retained. Only this new,
        # experiment-owned, byte-identified regenerable binary is removed.
        need(exe.parent==case and sha(exe)==row['binary_sha256'],'Cleanup target drift');exe.unlink()
    for q,h in m['includes'].items():need(sha(P/q)==h,'Include changed during regeneration '+q)
    receipt={'python_version':sys.version,'python_optimization':sys.flags.optimize,'status':'ALL_FIVE_RAW_REGENERATIONS_PASS','manifest_sha256':sha(manifest_path),'script_sha256':sha(Path(__file__)),'compiler_sha256':sha(cc),'compiler_version':version,'seconds':time.monotonic()-beg,'records':records,'parameters':m['parameters'],'cleanup':'Only the five newly generated binaries were removed after exact output-hash checks. Sources, numerical outputs and receipts retained.','trust':m['trust']}
    temp=out/'RECEIPT.pending';temp.write_text(json.dumps(receipt,indent=2)+'\n');os.replace(temp,out/'RECEIPT.json');print(json.dumps({'status':receipt['status'],'seconds':receipt['seconds'],'receipt':str(out/'RECEIPT.json')}))
if __name__=='__main__':main()
