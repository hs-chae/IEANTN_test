#!/usr/bin/env python3
"""Run the exact structured-AST C subset; functional/source refinement is separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--n',type=int,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(0<=a.n<=2000000000000,'source admissible bound');out=a.out.resolve();need(not out.exists(),'fresh output');out.mkdir(parents=True)
    cc=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-exposure-maximal-20261109/evolution/work/environment-cold-v1/lean-4.34.0-rc2-linux/bin/clang');need(sha(cc)=='9fcd5fc4baeea9c449bcc9ca4b9db7714465107669498b0056a853f22f5f4def','pinned actual Clang')
    driver=out/'driver.c';driver.write_text('#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\nuint64_t rpc_quotient_count(uint64_t,uint64_t,uint64_t*,uint64_t*);\nstatic uint64_t small[1500000],large[1500000];\nint main(void){uint64_t n=rpc_quotient_count(UINT64_C('+str(a.n)+'),1500000,small,large);if(printf("%" PRIu64 "\\n",n)<0)return 1;return fflush(stdout)!=0;}\n')
    exe=out/'count';build=[str(cc),'-std=c2x','-O2','-isystem','/usr/lib/gcc/x86_64-linux-gnu/11/include',str(S/'c/verified_quotient_count.c'),str(driver),'-o',str(exe)]
    result=subprocess.run(build,capture_output=True);(out/'build.stdout').write_bytes(result.stdout);(out/'build.stderr').write_bytes(result.stderr);need(result.returncode==0,'actual build')
    start=time.monotonic()
    with(out/'stdout').open('wb')as o,(out/'stderr').open('wb')as e:
        run=subprocess.run(['/usr/bin/time','-v','-o',str(out/'rusage'),str(exe)],stdout=o,stderr=e,timeout=300)
    seconds=time.monotonic()-start;need(run.returncode==0,'actual source-counter run')
    raw=(out/'stdout').read_bytes();need(re.fullmatch(rb'[0-9]+\n',raw)is not None,'complete canonical output');rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',(out/'rusage').read_text())
    receipt={'status':'ACTUAL_STRUCTURED_AST_C_RUN_NOT_FULL_SOURCE_REFINEMENT_ACCEPTANCE','N':a.n,'pi_output':int(raw),'seconds':seconds,'peak_child_rss_bytes':int(rss[1])*1024 if rss else None,'source_sha256':sha(S/'c/verified_quotient_count.c'),'driver_sha256':sha(driver),'compiler_sha256':sha(cc),'executable_sha256':sha(exe),'stdout_sha256':sha(out/'stdout'),'rusage_sha256':sha(out/'rusage'),'build_command':build,'execution_command':[str(exe)],'seed':None,'trust_boundary':'Actual source-to-AST theorem compiled separately; complete optimized loop/source execution refinement and particular large numerical theorem may remain pending. Driver/library ownership and physical compiler/runtime/hardware association are explicit remaining boundaries.'}
    (out/'RUN.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
