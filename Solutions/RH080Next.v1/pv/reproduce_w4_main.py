#!/usr/bin/env python3
"""Compile and audit actual W4 MainIO-to-ANT consumers over accepted banks.

This is a source-associated overlay, not a new N24 source-cold computation.
Dependency objects are immutable hardlinks with unchanged source/receipt checks.
"""
import argparse,json,os,subprocess,sys
from pathlib import Path
from compile_verified_batch_linked import atomic,need,sha,read_json
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent
REPOSITORY=PROJECT.parents[1]
ROOTS=["W4FFTCertifiedNorm","FFTW4SourceCertificate","FFTW4MainNumerics",
       "FFTW4MainConsumers","PopulationEnvelopeConsumers","FFTW4MainAudit"]
MARKER=("W4_FULL_MAIN_ANT_AUDIT_PASS source-roots=6 matched-control=1 exact-types "
        "Std3 no-native numerical-norm-premises=0 zero-scheme-premises=0 fullMainIO-and-N24-consumed")

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--context",required=True,type=Path)
    ap.add_argument("--bank",required=True,action="append",type=Path)
    ap.add_argument("--run",required=True,type=Path)
    ap.add_argument("--memory-gib",type=int,default=128)
    a=ap.parse_args()
    need(not os.path.lexists(a.run),"Fresh actual W4 overlay required")
    need(1<=a.memory_gib<=300,"Worker memory allowance must remain within300GiB")
    command=[sys.executable,str(HERE/"compile_verified_batch_linked.py"),
        "--context",str(a.context.resolve()),"--run",str(a.run.resolve()),
        "--memory-gib",str(a.memory_gib),"--source-root",str(PROJECT/"primal/population"),
        "--source-root",str(REPOSITORY)]
    for bank in a.bank:command.extend(["--bank",str(bank.resolve())])
    for root in ROOTS:command.extend(["--root",root])
    subprocess.run(command,check=True)
    result=read_json(a.run/"RESULT.json")
    plan=read_json(a.run/"PLAN.json")
    need(result["status"]=="PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY","Associated compiler gate absent")
    need(plan["immutable_dependency_objects_hardlinked"]is True,"Dependency objects were not linked")
    need({r["module"]for r in plan["source_rows"]}.issuperset(ROOTS),"Not all six selected modules freshly compiled")
    out=a.run/"logs/FFTW4MainAudit.stdout";text=out.read_text()
    need(MARKER in text,"Exact W4 actual-main/ANT proof-value audit absent")
    need(text.count("W4_FULL_MAIN_ANT_ROOT ")==6,"Incomplete six-root W4 audit")
    need(text.count("W4_MATCHED_KERNEL_CONTROL ")==1,"Matched control audit absent")
    atomic(a.run/"W4_MAIN_ACCEPTANCE.json",dict(
        status="PASS_SOURCE_FIRST_W4_FULL_MAIN_ANT_ASSOCIATED",
        roots=ROOTS,context_sha256=sha(a.context),plan_sha256=sha(a.run/"PLAN.json"),
        compiler_result_sha256=sha(a.run/"RESULT.json"),audit_stdout_sha256=sha(out),
        wrapper_sha256=sha(Path(__file__)),source_cold=False,
        numerical_norm_premises=0,generalized_zero_premises=0,
        actual_full_main_N24_and_actual_prime_count_consumed=True,
        native_proof_leaves=False,compiler_correctness_proved=False,
        official_Comparator_acceptance=False))
    print("PASS source-associated actual W4 full-main ANT; no compiler verification claim")
if __name__=="__main__":main()
