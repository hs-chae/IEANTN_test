#!/usr/bin/env python3
"""Measure actual source-bound C exact counting; this receipt is not a Lean proof."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(ok,message):
    if not ok: raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def reference_sieve(n):
    bits=bytearray(b"\1")*(n+1)
    if n>=0:bits[0]=0
    if n>=1:bits[1]=0
    d=2
    while d<=n//d:
        if bits[d]:
            begin=d*d;bits[begin:n+1:d]=b"\0"*((n-begin)//d+1)
        d+=1
    return sum(bits)
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--bounds",default="10,1000,100000,1000000");a=ap.parse_args()
    bounds=[int(s)for s in a.bounds.split(",")];need(bounds and len(bounds)==len(set(bounds)) and all(0<=n<=100000000 for n in bounds),"bounded distinct exact uint64 inputs")
    out=a.out.resolve();need(not out.exists(),"fresh owned output");out.mkdir(parents=True)
    cc=Path("/ryu/hyunsik/playground/independence/codex/ivy/ieantn-exposure-maximal-20261109/evolution/work/environment-cold-v1/lean-4.34.0-rc2-linux/bin/clang")
    need(sha(cc)=="9fcd5fc4baeea9c449bcc9ca4b9db7714465107669498b0056a853f22f5f4def","pinned actual Clang binary")
    records=[]
    for n in bounds:
        driver=out/f"driver-{n}.c";exe=out/f"count-{n}";stdout=out/f"count-{n}.stdout";stderr=out/f"count-{n}.stderr";usage=out/f"count-{n}.rusage"
        driver.write_text('#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\nuint64_t rpc_count(uint64_t);\nint main(void) { uint64_t n=rpc_count(UINT64_C('+str(n)+')); if(printf("%" PRIu64 "\\n",n)<0) return 1; return fflush(stdout)!=0; }\n')
        command=[str(cc),"-std=c2x","-O2","-isystem","/usr/lib/gcc/x86_64-linux-gnu/11/include",str(S/"c/verified_primecount.c"),str(driver),"-o",str(exe)]
        build=subprocess.run(command,capture_output=True);(out/f"build-{n}.stdout").write_bytes(build.stdout);(out/f"build-{n}.stderr").write_bytes(build.stderr);need(build.returncode==0,"actual C build")
        start=time.monotonic()
        with stdout.open("wb")as o,stderr.open("wb")as e:
            run=subprocess.run(["/usr/bin/time","-v","-o",str(usage),str(exe)],stdout=o,stderr=e,timeout=120)
        seconds=time.monotonic()-start;need(run.returncode==0,"actual C run")
        raw=stdout.read_bytes();need(re.fullmatch(rb"[0-9]+\n",raw)is not None,"exact canonical count stdout");count=int(raw)
        reference=reference_sieve(n);need(count==reference,"independent ordinary Python sieve agreement")
        rss=re.search(r"Maximum resident set size \(kbytes\): ([0-9]+)",usage.read_text())
        records.append({"bound":n,"count":count,"independent_sieve_count":reference,"c_execution_seconds":seconds,"actual_peak_child_rss_bytes":int(rss[1])*1024 if rss else None,"source_sha256":sha(S/"c/verified_primecount.c"),"driver_sha256":sha(driver),"executable_sha256":sha(exe),"stdout_sha256":sha(stdout),"rusage_sha256":sha(usage),"build_command":command,"execution_command":[str(exe)],"generic_compiler_runtime_hardware_boundary_retained":True})
    result={"status":"ACTUAL_C_COUNT_BENCHMARK_ONLY_NOT_A_LEAN_EXECUTION_PROOF","random_seed":None,"compiler_sha256":sha(cc),"source_sha256":sha(S/"c/verified_primecount.c"),"script_sha256":sha(__file__),"records":records}
    (out/"BENCHMARK.json").write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result,indent=2))
if __name__=="__main__":main()
