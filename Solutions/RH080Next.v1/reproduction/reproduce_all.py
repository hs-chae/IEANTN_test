#!/usr/bin/env python3
"""Plan or execute fresh public RH080 reproduction pipelines.

A plan, an old campaign receipt, and a successful child exit are not a new
whole-campaign acceptance. Heavy stages require the existing owned-resource
supervisor. No prior application object bank is accepted by this entry point.
"""
from __future__ import annotations
import argparse,importlib.util,importlib.metadata,json,os,shutil,subprocess,sys,time
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha,validate_context

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent
REPOSITORY=PROJECT.parents[1]
PYTHON=sys.executable
ORDER=["source-fixtures","gaussian-inputs","gaussian","dual","population",
       "analytic-flat64","analytic-family","analytic-asymptotic",
       "finite-inputs","finite-main","canonical-finite",
       "n24-inputs","n24-compact","n24-kernel","n24-bank","w4-main","canonical-w4","c7-kernel-control",
       "exposure","physical"]
DEPS={
 "gaussian":["gaussian-inputs"],"finite-main":["finite-inputs"],
 "canonical-finite":["finite-main"],"n24-compact":["n24-inputs"],"n24-kernel":["n24-compact"],
 "n24-bank":["n24-kernel"],"w4-main":["n24-bank","finite-main","population"],
 "canonical-w4":["w4-main","canonical-finite","analytic-flat64","analytic-family","analytic-asymptotic","population"],
 "c7-kernel-control":["canonical-w4","w4-main"],
 "physical":["source-fixtures"],
}
PROTECTED={"gaussian","dual","population","finite-main","canonical-finite",
           "n24-inputs","n24-kernel","w4-main","canonical-w4","c7-kernel-control","exposure"}
REQUIRED={
 "source-fixtures":["pv/check_regeneration.py"],
 "gaussian-inputs":["primal/generate_scaled_gaussian.py","primal/generate_scaled_fourier.py","primal/generate_scaled_assembly.py"],
 "gaussian":["primal/reproduce_cold.py"],
 "dual":["dual/reproduce_dual.py","reproduction/regenerate_dual_fixture.py"],
 "population":["primal/population/reproduce.py"],
 "analytic-flat64":["explicit/reproduce_analytic_flat64.py"],
 "analytic-family":["explicit/reproduce_analytic_flat_family.py"],
 "analytic-asymptotic":["explicit/reproduce_analytic_flat_family_asymptotic.py"],
 "finite-inputs":["dual/produce_fft_forest_certificate.py","pv/final_fap_source_data_v2.py","pv/evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json"],
 "finite-main":["pv/reproduce_final_fap_source_cold_v2.py"],
 "canonical-finite":["pv/compile_verified_batch_linked.py","explicit/verify_canonical_evolution.py","explicit/CANONICAL_EVOLUTION_BASELINE.json"],
 "n24-inputs":["dual/produce_fft_dag_certificate.py","dual/evidence/W4_N24_EXPECTED_INPUTS.json"],
 "n24-compact":["compact-proof-repair-v1/tools/derive_compact_candidate.py","compact-proof-repair-v1/tools/compact_contract.py","compact-proof-repair-v1/tools/generate_compact_final_v2.py","compact-proof-repair-v1/locked/w4-input.json","compact-proof-repair-v1/locked/original-candidate-24.json","compact-proof-repair-v1/locked/original-foundations-24.json","compact-proof-repair-v1/locked/mathematical-source-identities-24.json","compact-proof-repair-v1/locked/original-tool-identities.json"],
 "n24-kernel":["dual/reproduce_fft_dag_physical_v2.py","dual/reproduce_fft_dag_v2.py","dual/verify_fft_dag_fresh_v3.py","compact-proof-repair-v1/tools/verify_fresh_compact.py","compact-proof-repair-v1/tools/compact_contract.py","pv/supervise_resource_run.py"],
 "n24-bank":["compact-proof-repair-v1/tools/export_fresh_compact.py","compact-proof-repair-v1/tools/verify_fresh_compact.py","compact-proof-repair-v1/tools/compact_contract.py"],
 "w4-main":["pv/reproduce_w4_main_v2.py","pv/compile_verified_batch_linked_v2.py","pv/lean/FFTW4MainAudit.lean"],
 "canonical-w4":["explicit/reproduce_canonical_w4_evolution_v2.py","explicit/verify_canonical_w4_evolution_v4.py","explicit/CANONICAL_W4_BASELINE.json","explicit/CanonicalW4EvolutionAudit.lean"],
 "c7-kernel-control":["pv/compile_verified_batch_linked_v2.py","pv/lean/C7KernelScalars.lean","pv/lean/C7KernelGlobal.lean","pv/lean/C7KernelAudit.lean"],
 "exposure":["ablation/review/reproduce_clean_proofs.py"],
 "physical":["pv/reproduce_recursive_physical.py","pv/verify_recursive_physical_receipts.py","pv/test_recursive_physical_receipts.py"],
}
ANALYTIC={
 "analytic-flat64":("explicit/reproduce_analytic_flat64.py","PASS_SOURCE_COLD_KERNEL_ONLY_ANALYTIC_ANT",20),
 "analytic-family":("explicit/reproduce_analytic_flat_family.py","PASS_SOURCE_COLD_KERNEL_ONLY_ANALYTIC_ANT",21),
 "analytic-asymptotic":("explicit/reproduce_analytic_flat_family_asymptotic.py","PASS_SOURCE_COLD_REAL_ALPHA_ASYMPTOTIC_ANALYTIC_ANT_NOT_PV",23),
}
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);return module

def available_ram():
    return int(next(x.split()[1]for x in Path("/proc/meminfo").read_text().splitlines()if x.startswith("MemAvailable:")))*1024

class Runner:
    def __init__(self,args):
        self.a=args;self.root=args.run.resolve();self.context=args.context.resolve()
        self.commands=[];self.completed={};self.supervisors={};self.started_stages=set()
    def stage(self,name):
        p=self.root/name;p.mkdir(parents=True,exist_ok=True);return p
    def call(self,stage,tag,cmd,protected=False):
        folder=self.stage(stage);out=folder/(tag+".stdout");err=folder/(tag+".stderr")
        need(not out.exists()and not err.exists(),"Fresh command evidence required")
        start=time.monotonic();supervisor=None
        if protected:
            supervisor=folder/(tag+".SUPERVISOR.json")
            command_plan=folder/(tag+".COMMAND.json")
            sources={str(HERE/"reproduce_all.py"),str(PROJECT/"pv/supervise_resource_run.py")}
            sources.update(str(PROJECT/x)for x in REQUIRED[stage]if x.endswith(".py"))
            atomic(command_plan,dict(command=list(map(str,cmd)),
                source_pins=[dict(path=x,sha256=sha(Path(x)))for x in sorted(sources)]))
            actual=[PYTHON,str(PROJECT/"pv/supervise_resource_run.py"),
                    "--root",str(self.root),"--command",str(command_plan),
                    "--receipt",str(supervisor),"--live",str(folder/(tag+".LIVE.json"))]
        else:actual=list(map(str,cmd))
        with out.open("xb")as o,err.open("xb")as e:
            child=subprocess.run(actual,cwd=REPOSITORY,stdout=o,stderr=e,
                env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1",GIT_OPTIONAL_LOCKS="0"))
        row=dict(stage=stage,tag=tag,command=list(map(str,cmd)),actual_command=actual,
            returncode=child.returncode,seconds=time.monotonic()-start,
            stdout_sha256=sha(out),stderr_sha256=sha(err))
        if not protected:self.started_stages.add(stage)
        elif supervisor.is_file()and type(read_json(supervisor).get("returncode"))is int:self.started_stages.add(stage)
        row["selected_pipeline_started"]=stage in self.started_stages
        self.commands.append(row);atomic(folder/(tag+".COMMAND_RESULT.json"),row)
        need(child.returncode==0,"Public pipeline failed: "+stage+"/"+tag)
        if supervisor:
            receipt=read_json(supervisor)
            need(receipt["status"]=="COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE"and
                 receipt["returncode"]==0 and receipt["failure"]is None,"Resource supervisor did not complete")
            self.supervisors[stage]=dict(receipt=supervisor,command_plan=command_plan,
                stdout=supervisor.with_suffix(".stdout"),stderr=supervisor.with_suffix(".stderr"))
        return out
    def result(self,stage,path,status,counts=None):
        r=read_json(path);need(r.get("status")==status,"Unexpected actual result status: "+stage)
        for k,v in (counts or {}).items():need(type(r.get(k))is type(v)and r.get(k)==v,"Actual scope differs: "+stage+"/"+k)
        record=dict(status="PASS_NEW_EXECUTION",result=str(path),result_sha256=sha(path),
            public_status=status,scope=counts or {})
        self.completed[stage]=record;atomic(self.stage(stage)/"STAGE_RESULT.json",record);return r
    def banks(self,names):
        return [self.root/n/("bank"if n=="population"or n in ANALYTIC else"work")for n in names]
    def analytic(self,name):
        script,status,count=ANALYTIC[name];work=self.stage(name)/"work"
        self.call(name,"compile",[PYTHON,str(PROJECT/script),"--context",str(self.context),"--run",str(work)])
        bank=self.stage(name)/"bank"
        self.call(name,"format-export",[PYTHON,str(HERE/"export_simple_analytic_bank.py"),
            "--context",str(self.context),"--base",str(work),"--run",str(bank)])
        self.result(name,work/"RESULT.json",status,dict(modules=count,source_cold=True))
    def run_stage(self,name):
        folder=self.stage(name);work=folder/"work"
        if name in ANALYTIC:return self.analytic(name)
        if name=="source-fixtures":
            out=self.call(name,"regenerate",[PYTHON,str(PROJECT/"pv/check_regeneration.py")])
            value=read_json(out);need(value["status"]=="PASS_DETERMINISTIC_SOURCE_AST_REGENERATION","Source/AST regeneration gate absent")
            atomic(folder/"RESULT.json",value);return self.result(name,folder/"RESULT.json",value["status"])
        if name=="gaussian-inputs":
            candidate=PROJECT/"primal/scaled40/CANDIDATE.json"
            self.call(name,"cells",[PYTHON,str(PROJECT/"primal/generate_scaled_gaussian.py"),
                "--candidate",str(candidate),"--out",str(folder/"cells"),
                "--denom","32","--root-denom","32768","--chunk-size","32"])
            self.call(name,"fourier",[PYTHON,str(PROJECT/"primal/generate_scaled_fourier.py"),
                "--candidate",str(candidate),"--out",str(folder/"fourier")])
            self.call(name,"assembly",[PYTHON,str(PROJECT/"primal/generate_scaled_assembly.py"),
                "--cells",str(folder/"cells"),"--out",str(folder/"assembly")])
            identities=[]
            for directory in [folder/"cells/source",folder/"fourier",folder/"assembly"]:
                for p in sorted(directory.glob("*.lean")):
                    original=PROJECT/"primal/scaled40"/p.name
                    need(original.is_file()and sha(p)==sha(original),"Regenerated Gaussian proof input differs: "+p.name)
                    identities.append(dict(file=p.name,sha256=sha(p)))
            need(identities,"No Gaussian inputs regenerated")
            atomic(folder/"RESULT.json",dict(status="PASS_REGENERATED_GAUSSIAN_INPUT_IDENTITIES",
                candidate_sha256=sha(candidate),files=identities,untrusted_numerical_proposals=True))
            return self.result(name,folder/"RESULT.json","PASS_REGENERATED_GAUSSIAN_INPUT_IDENTITIES")
        if name=="gaussian":
            self.call(name,"compile",[PYTHON,str(PROJECT/"primal/reproduce_cold.py"),
                "--context",str(self.context),"--out",str(work),"--workers","2","--worker-memory-gib","64"],True)
            return self.result(name,work/"RESULT.json","PASS_COMPLETE_SCALED40_CERTIFICATE_TRUE_FOURIER_CMS_V4_CONSUMERS",
                dict(modules=92,full_clean_cold_reproduction=True,newly_compiled_modules=92))
        if name=="dual":
            fixture=[PYTHON,str(HERE/"regenerate_dual_fixture.py"),"--run",str(folder/"fixed-source")]
            if self.a.cc:fixture += ["--cc",self.a.cc]
            self.call(name,"regenerate-and-observe",fixture)
            need(read_json(folder/"fixed-source/RESULT.json")["status"]==
                "PASS_REGENERATED_DUAL_FRONTEND_AND_FIXED_C_OBSERVATION","Fixed dual source/run association incomplete")
            self.call(name,"compile",[PYTHON,str(PROJECT/"dual/reproduce_dual.py"),
                "--repository",str(REPOSITORY),"--context",str(self.context),"--run",str(work),"--workers","4"],True)
            return self.result(name,work/"RESULT.json","PASS_FRESH_SOURCE_FIRST_FULL_CMS_CLOSURE_STANDARD_AXIOMS_ONLY",dict(modules=49,theorems=11))
        if name=="population":
            self.call(name,"compile",[PYTHON,str(PROJECT/"primal/population/reproduce.py"),
                "--context",str(self.context),"--out",str(work),"--workers","2","--worker-memory-gib","64"],True)
            self.call(name,"format-export",[PYTHON,str(HERE/"export_population_bank.py"),
                "--base",str(work),"--context",str(self.context),"--run",str(folder/"bank")])
            return self.result(name,work/"RESULT.json","PASS_COMPLETE_SOURCE_FIRST_NUMERICAL_FOURIER_EVENTUAL_PRIME_POPULATION_AND_MATCHED_CONTROL",
                dict(modules=91,full_source_cold=True))
        if name=="finite-inputs":
            self.call(name,"generate",[PYTHON,str(PROJECT/"dual/produce_fft_forest_certificate.py"),
                "--stages","17","--out",str(work)])
            helper=load_module("rh080_literal_data",PROJECT/"pv/final_fap_source_data_v2.py")
            inputs=read_json(PROJECT/"pv/evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json")
            candidate=read_json(work/"PLAN.json")
            need(candidate["n"]==131072 and candidate["norm_numerator"]==781796015790084776,
                "Regenerated finite mathematical parameters differ")
            rows=[]
            for item in inputs["sources"]:
                origin=REPOSITORY/item["path"]
                if item["path"].startswith("Solutions/RH080Next.v1/generated/fap17/"):
                    origin=work/Path(item["path"]).name
                need(origin.is_file()and sha(origin)==item["sha256"],"Regenerated/pinned finite source differs: "+item["module"])
                rows.append(dict(module=item["module"],source_origin=str(origin),source_sha256=item["sha256"]))
            data=[]
            for raw in inputs["data"]:
                row={k:v for k,v in raw.items()if k!="path"}
                row["source_origin"]=str((work/Path(raw["path"]).name).resolve());data.append(row)
            checked=helper.inventory_data(data,rows)
            need(len(rows)==681 and len(checked)==34 and sum(x["bytes"]for x in checked)==inputs["literal_data_bytes"],
                "Finite source/literal-data scope differs")
            atomic(folder/"SOURCE_INVENTORY.json",dict(schema_version=2,full_dependency_cone=rows,
                literal_data=checked,literal_data_helper_sha256=sha(PROJECT/"pv/final_fap_source_data_v2.py"),
                portable_inputs_sha256=sha(PROJECT/"pv/evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json"),
                numerical_producer_sha256=sha(PROJECT/"dual/produce_fft_forest_certificate.py")))
            atomic(folder/"RESULT.json",dict(status="PASS_REGENERATED_FINITE_SOURCE_AND34_LITERAL_DATA_IDENTITIES",
                modules=681,literal_data_files=34,literal_data_bytes=inputs["literal_data_bytes"],
                numerical_inputs_regenerated_not_copied_from_study_bank=True))
            return self.result(name,folder/"RESULT.json","PASS_REGENERATED_FINITE_SOURCE_AND34_LITERAL_DATA_IDENTITIES",
                dict(modules=681,literal_data_files=34))
        if name=="finite-main":
            self.call(name,"compile",[PYTHON,str(PROJECT/"pv/reproduce_final_fap_source_cold_v2.py"),
                "--context",str(self.context),"--inventory",str(self.root/"finite-inputs/SOURCE_INVENTORY.json"),
                "--run",str(work),"--scratch-root",str(self.root),"--workers","2",
                "--worker-memory-gib","128","--root","FFTFapMainAudit"],True)
            self.call(name,"reverify",[PYTHON,str(PROJECT/"pv/reproduce_final_fap_source_cold_v2.py"),
                "--verify-only",str(work)])
            return self.result(name,work/"RESULT.json","PASS_COMPLETE_FINITE_FAP_FULL_MAIN_ANT_SOURCE_COLD",
                dict(modules=681,literal_data_files=34))
        if name=="n24-inputs":
            self.call(name,"generate",[PYTHON,str(PROJECT/"dual/produce_fft_dag_certificate.py"),
                "--stages","24","--chunk-log","13","--pairs-per-module","524288","--out",str(work)],True)
            proposal=read_json(work/"PLAN.json")
            expected=read_json(PROJECT/"dual/evidence/W4_N24_EXPECTED_INPUTS.json")
            for key in ["stages","n","chunk","pairs_per_module","namespace","final_module",
                        "input_sha256","producer_sha256","norm_numerator","total_abs","quad"]:
                need(proposal[key]==expected[key],"Fixed original N24 input identity differs: "+key)
            need(proposal["modules"]==expected["generated_modules"]and proposal["payloads"]==expected["payloads"],
                "Original1020 generated Lean/937CSV expected byte inventories differ")
            need(proposal["n"]==16777216 and proposal["norm_numerator"]==7813568381279800
                and len(proposal["payloads"])==937,"Regenerated N24 proposal differs")
            for kind,key in [("modules","sha256"),("payloads","sha256")]:
                for item in proposal[kind]:need(sha(work/item["file"])==item[key],"New N24 proposal identity differs")
            atomic(folder/"RESULT.json",dict(status="PASS_REGENERATED_FIXED_N24_UNTRUSTED_PROPOSAL_IDENTITIES",
                N=16777216,norm_numerator=7813568381279800,CSV_files=937,mathematical_proof=False))
            return self.result(name,folder/"RESULT.json","PASS_REGENERATED_FIXED_N24_UNTRUSTED_PROPOSAL_IDENTITIES")
        if name=="n24-compact":
            original=self.root/"n24-inputs/work"
            self.call(name,"derive-source-only",[PYTHON,str(PROJECT/"compact-proof-repair-v1/tools/derive_compact_candidate.py"),
                "--candidate",str(original),"--out",str(work),"--project-root",str(PROJECT)])
            transformed=read_json(work/"PROOF_TRANSFORM_RECEIPT.json")
            need(transformed.get("status")=="PASS_SOURCE_ONLY_TRANSFORM_NOT_PROOF_NOT_PV",
                "Compact source derivation did not pass its locked contract")
            derived=read_json(work/"PLAN.json");old=read_json(original/"PLAN.json")
            need(len(old["modules"])==1020 and len(derived["modules"])==1022,
                "Original and compact source inventories differ")
            need(derived["payloads"]==old["payloads"] and len(derived["payloads"])==937,
                "Compact derivation changed numerical payload identities")
            need(sha(work/"ORIGINAL_PRODUCER_PLAN.json")==sha(original/"PLAN.json"),
                "The original numerical producer PLAN was not preserved")
            atomic(folder/"RESULT.json",dict(status="PASS_SOURCE_ONLY_COMPACT_DERIVATION_NOT_PROOF_NOT_PV",
                original_generated_modules=1020,derived_generated_modules=1022,unchanged_CSV_files=937,
                original_plan_sha256=sha(original/"PLAN.json"),derived_plan_sha256=sha(work/"PLAN.json"),
                transform_receipt_sha256=sha(work/"PROOF_TRANSFORM_RECEIPT.json"),
                mathematical_proof=False,source_first_PV_complete=False))
            return self.result(name,folder/"RESULT.json","PASS_SOURCE_ONLY_COMPACT_DERIVATION_NOT_PROOF_NOT_PV")
        if name=="n24-kernel":
            candidate=self.root/"n24-compact/work"
            command=[PYTHON,"-u",str(PROJECT/"dual/reproduce_fft_dag_physical_v2.py"),
                "--context",str(self.context),"--candidate",str(candidate),"--run",str(work),
                "--workers",str(self.a.n24_workers),"--worker-virtual-as","unlimited"]
            self.call(name,"compile",command,True)
            proof=self.supervisors[name];gate=folder/"INDEPENDENT_ACCEPTED.json"
            self.call(name,"independent-gate",[PYTHON,str(PROJECT/"compact-proof-repair-v1/tools/verify_fresh_compact.py"),
                "--run",str(work),"--context",str(self.context),"--candidate",str(candidate),
                "--project-root",str(PROJECT),
                "--output",str(gate),"--supervisor",str(proof["receipt"]),
                "--command-plan",str(proof["command_plan"]),"--stdout",str(proof["stdout"]),
                "--stderr",str(proof["stderr"]),"--unit",self.a.unit])
            need(gate.is_file(),"Independent fresh compact N24 acceptance absent")
            independent=read_json(gate)
            need(independent.get("status")=="PASS_INDEPENDENT_FRESH_COMPACT_W4_KERNEL_ONLY_NOT_C_PV"
                and type(independent.get("modules"))is int and independent["modules"]==1035
                and independent.get("source_cold")is True and independent.get("toy_only")is False,
                "Complete production compact N24 independent gate absent")
            return self.result(name,work/"RESULT.json","PASS_W4_COMPLETE_INTEGER_FFT_TRACE_CHECKED_TWIDDLES_AND_NUMERATOR_NOT_SOURCE_PV",
                dict(modules=1035,N=16777216,audited_roots=29))
        if name=="n24-bank":
            self.call(name,"format-export",[PYTHON,str(PROJECT/"compact-proof-repair-v1/tools/export_fresh_compact.py"),
                "--base",str(self.root/"n24-kernel/work"),"--context",str(self.context),
                "--candidate",str(self.root/"n24-compact/work"),"--project-root",str(PROJECT),
                "--accepted",str(self.root/"n24-kernel/INDEPENDENT_ACCEPTED.json"),"--run",str(work)])
            need((work/"PLAN.json").is_file()and(work/"RESULT.json").is_file(),"Format-only compact N24 bank absent")
            exported=read_json(work/"RESULT.json")
            need(exported.get("status")=="PASS_FORMAT_ONLY_ACCEPTED_FRESH_COMPACT_BANK_NO_NEW_COMPILATION"
                and type(exported.get("sources"))is int and exported["sources"]==1035
                and type(exported.get("objects"))is int and exported["objects"]==1035,
                "Complete compact N24 format export absent")
            atomic(folder/"RESULT.json",dict(status="PASS_FORMAT_ONLY_NEW_N24_BANK",
                original_gate_sha256=sha(self.root/"n24-kernel/INDEPENDENT_ACCEPTED.json"),
                format_result_sha256=sha(work/"RESULT.json"),new_mathematical_claim=False))
            return self.result(name,folder/"RESULT.json","PASS_FORMAT_ONLY_NEW_N24_BANK")
        if name=="w4-main":
            command=[PYTHON,str(PROJECT/"pv/reproduce_w4_main_v2.py"),"--context",str(self.context),
                "--run",str(work),"--memory-gib","300","--worker-virtual-as","unlimited"]
            for bank in self.banks(["n24-bank","finite-main","population"]):command+=["--bank",str(bank)]
            self.call(name,"compile",command,True)
            return self.result(name,work/"W4_MAIN_ACCEPTANCE.json","PASS_SOURCE_FIRST_W4_FULL_MAIN_ANT_ASSOCIATED")
        if name=="canonical-finite":
            command=[PYTHON,str(PROJECT/"pv/compile_verified_batch_linked.py"),
                "--context",str(self.context),"--run",str(work),"--memory-gib","128",
                "--source-root",str(PROJECT/"primal/finite"),"--source-root",str(PROJECT/"primal/population"),
                "--source-root",str(REPOSITORY),"--root","CanonicalEvolutionAudit",
                "--bank",str(self.root/"finite-main/work")]
            self.call(name,"compile",command,True)
            verification=folder/"verification"
            self.call(name,"exact-claim-gate",[PYTHON,str(PROJECT/"explicit/verify_canonical_evolution.py"),
                "--context",str(self.context),"--bank",str(work),
                "--baseline",str(PROJECT/"explicit/CANONICAL_EVOLUTION_BASELINE.json"),
                "--out",str(verification)])
            checked=read_json(verification/"RESULT.json")
            need(checked["status"]=="PASS_LOCAL_CANONICAL_EVOLUTION_PROOFS_AND_DISJOINT_ENTRY_POINTS_NO_COMPARATOR",
                "Finite canonical exact-claim/disjoint-entry gate incomplete")
            atomic(work/"CANONICAL_ACCEPTANCE.json",dict(status="PASS_CANONICAL_EXACT_CLAIMS_AND_DEPENDENCIES",
                scope="finite",verification_result_sha256=sha(verification/"RESULT.json"),
                original_v1_files_unchanged=23,official_Comparator_receipt=False,
                oom_counter_status="Public historical verifier literal is not telemetry; see owned supervisor separately"))
            return self.result(name,work/"RESULT.json","PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY")
        if name=="canonical-w4":
            command=[PYTHON,str(PROJECT/"explicit/reproduce_canonical_w4_evolution_v2.py"),
                "--context",str(self.context),"--run",str(work),"--memory-gib","300","--worker-virtual-as","unlimited"]
            banks=self.banks(["finite-main","n24-bank","w4-main","population","canonical-finite"])
            banks += [self.root/n/"bank"for n in ANALYTIC]
            for bank in banks:command+=["--bank",str(bank)]
            # Selecting the final audit compiles its complete transitive source
            # closure; the independent reader pins this exact root selection.
            command += ["--root","CanonicalW4EvolutionAudit"]
            self.call(name,"compile",command,True)
            verification=folder/"verification"
            self.call(name,"exact-claim-gate",[PYTHON,str(PROJECT/"explicit/verify_canonical_w4_evolution_v4.py"),
                "--context",str(self.context),"--bank",str(work),
                "--baseline",str(PROJECT/"explicit/CANONICAL_W4_BASELINE.json"),
                "--out",str(verification),"--memory-gib","300","--worker-virtual-as","unlimited"])
            gate=verification/"CANONICAL_ACCEPTANCE.json"
            need(gate.is_file(),"Separate canonical exact-claim acceptance is absent")
            accepted=read_json(gate)
            need(accepted.get("status")=="PASS_CANONICAL_EXACT_CLAIMS_AND_DEPENDENCIES"
                and accepted.get("scope")=="w4","Canonical W4 exact-claim gate absent")
            return self.result(name,work/"RESULT.json","PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY")
        if name=="c7-kernel-control":
            need(not os.path.lexists(folder/"C7_CONTROL_ACCEPTANCE.json") and
                not os.path.lexists(folder/"STAGE_RESULT.json"),"Fresh C7 terminal receipts required")
            command=[PYTHON,str(PROJECT/"pv/compile_verified_batch_linked_v2.py"),
                "--context",str(self.context),"--bank",str(self.root/"canonical-w4/work"),
                "--bank",str(self.root/"w4-main/work"),"--root","C7KernelAudit",
                "--run",str(work),"--memory-gib","300","--worker-virtual-as","unlimited"]
            # The public helper already searches PROJECT/pv/lean. Repeating that
            # same --source-root would create an ambiguous duplicate candidate.
            self.call(name,"compile-and-audit",command,True)
            generic=read_json(work/"RESULT.json")
            need(generic.get("status")=="PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY" and
                type(generic.get("modules"))is int and generic["modules"]==3,"C7 fresh compiler scope differs")
            audit=work/"logs/C7KernelAudit.stdout";need(audit.is_file(),"C7 actual audit stdout absent")
            marker="C7_FULL_KERNEL_CONTROL_PASS exact-PV-and-FFT-only-control-types same-W4-2520-coefficients same-N24-norm same-ANT-residual-consumer Std3 no-native four-opaque-kernel-scalar-certificates no-new-numerical-premise unused-source-containing-imports-disclosed POSTHOC-NON-PV"
            text=audit.read_text();need(text.splitlines().count(marker)==1,"Exact complete C7 proof-value audit did not pass")
            for required in ["C7_FULL_KERNEL_CONTROL_AXIOMS","C7_PURE_N24_MODULE_GRAPH appmodules=1059 declarations=",
                             "C7_FULL_KERNEL_CONTROL_PROOF_CLOSURE names=","actual-C-source-correspondence-run=0",
                             "C7_PRUNED_PURE_DATA_BOUNDARIES"]:
                need(required in text,"Required C7 audit evidence missing: "+required)
            atomic(folder/"C7_CONTROL_ACCEPTANCE.json",dict(status="PASS_POSTHOC_FULL_KERNEL_NONPV_W4_CONTROL_SAME_PREMISES",
                result_sha256=sha(work/"RESULT.json"),audit_stdout_sha256=sha(audit),
                final_theorem="RH080Next.PosthocKernelControl.matched_fully_kernel_global",
                final_theorem_axiom_roots=1,actual_type_comparisons=2,scalar_caps=8,
                opaque_kernel_scalar_certificates=4,existing_rational_bridge_facts=4,
                original_N24_norm_same=True,ANT_residual_consumer_same=True,
                source_free_proof_value_path_checked=True,source_free_module_import_graph_claimed=False,
                source_free_elaborator_IO_claimed=False,posthoc_not_primary_trial=True,
                source_first_PV=False,full_new_heavy681_orN24_replay_claimed=False))
            return self.result(name,folder/"C7_CONTROL_ACCEPTANCE.json","PASS_POSTHOC_FULL_KERNEL_NONPV_W4_CONTROL_SAME_PREMISES")
        if name=="exposure":
            self.call(name,"compile",[PYTHON,str(PROJECT/"ablation/review/reproduce_clean_proofs.py"),
                "--context",str(self.context),"--out",str(work),"--workers","4",
                "--memory-gib","64","--scratch-root",str(self.root)],True)
            return self.result(name,work/"RESULT.json","PASS_PORTABLE_COMMON169_PLUS_ALL13_LOCKED15_LEAN_SOURCE_COLD_STD3",
                dict(common_modules=169,locked_trials=13,locked_source_modules=15,compile_commands=199))
        if name=="physical":
            work.mkdir()
            pin=load_module("rh080_physical_verifier",PROJECT/"pv/verify_recursive_physical_receipts.py")
            cc=Path(self.a.cc or shutil.which("gcc-11")or shutil.which("gcc")or "").resolve()
            need(cc.is_file()and sha(cc)==pin.COMPILER_SHA,"Exact documented physical GCC compiler is unavailable; no host installation is attempted")
            for suffix,opt in [("",[]),("-O",["-O"]),("-OO",["-OO"])]:
                self.call(name,"observe"+(suffix or "-normal"),[PYTHON]+opt+[str(PROJECT/"pv/reproduce_recursive_physical.py"),
                    "--run",str(work/("recursive-physical-final"+suffix+"-v1")),"--cc",str(cc)])
            for suffix,opt in [("normal",[]),("O",["-O"]),("OO",["-OO"])]:
                self.call(name,"verify-"+suffix,[PYTHON]+opt+[str(PROJECT/"pv/verify_recursive_physical_receipts.py"),
                    "--runs-root",str(work),"--source-root",str(PROJECT/"pv"),
                    "--output",str(folder/("ACCEPTED-"+suffix+".json"))])
            self.call(name,"negative-controls",[PYTHON,str(PROJECT/"pv/test_recursive_physical_receipts.py"),
                "--runs-root",str(work),"--run",str(folder/"negative-controls")])
            return self.result(name,folder/"ACCEPTED-normal.json","PASS_24_RETAINED_PHYSICAL_OBSERVATIONS_NOT_SEMANTIC_PROOF")
        raise ValueError("Unimplemented stage "+name)

def select(requested):
    selected=set(ORDER if "all"in requested else requested)
    need(selected<=set(ORDER),"Unknown stage")
    def add(n):
        for d in DEPS.get(n,[]):
            if d not in selected:selected.add(d);add(d)
    for n in list(selected):add(n)
    return[n for n in ORDER if n in selected]

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--context",required=True,type=Path);ap.add_argument("--run",required=True,type=Path)
    ap.add_argument("--stages",nargs="+",default=["all"],choices=["all"]+ORDER)
    ap.add_argument("--execute",action="store_true")
    ap.add_argument("--n24-workers",type=int,default=12)
    ap.add_argument("--unit",help="Owned300GiB/noSwap service name for full production resource gates")
    ap.add_argument("--cc",help="Exact retained physical GCC compiler path")
    a=ap.parse_args();need(1<=a.n24_workers<=32,"Bounded N24 worker population")
    need(not os.path.lexists(a.run),"Fresh reproduction output required")
    c,roots=validate_context(read_json(a.context));stages=select(a.stages)
    missing=[dict(stage=n,path=x)for n in stages for x in REQUIRED[n]if not(PROJECT/x).is_file()]
    prerequisites=[]
    if "canonical-w4"in stages:
        try:yaml_version=importlib.metadata.version("PyYAML")
        except importlib.metadata.PackageNotFoundError:yaml_version=None
        prerequisites.append(dict(kind="python_package",name="PyYAML",required_version="6.0.3",
            actual_version=yaml_version,available=yaml_version=="6.0.3"))
    if "physical"in stages:
        validator=load_module("rh080_physical_preflight",PROJECT/"pv/verify_recursive_physical_receipts.py")
        cc=Path(a.cc or shutil.which("gcc-11")or shutil.which("gcc")or "").resolve()
        valid=cc.is_file()and sha(cc)==validator.COMPILER_SHA
        prerequisites.append(dict(kind="pinned_physical_C_compiler",path=str(cc),available=valid,
            required_sha256=validator.COMPILER_SHA,required_version=validator.COMPILER_VERSION))
    for name in ["git","prlimit","time"]:
        found=shutil.which(name)
        prerequisites.append(dict(kind="executable",name=name,path=found,available=found is not None))
    source_pins={str(Path(__file__).resolve()):sha(Path(__file__)),
        str(HERE/"bootstrap_context.py"):sha(HERE/"bootstrap_context.py"),
        str(HERE/"export_simple_analytic_bank.py"):sha(HERE/"export_simple_analytic_bank.py"),
        str(HERE/"export_population_bank.py"):sha(HERE/"export_population_bank.py")}
    for stage in stages:
        for relative in REQUIRED[stage]:
            path=PROJECT/relative
            if path.is_file():source_pins[str(path)]=sha(path)
    a.run.mkdir(parents=True)
    plan=dict(status="EXECUTION_REQUESTED"if a.execute else"PLAN_ONLY_NOT_REPRODUCED",
        stages=stages,missing_public_interfaces=missing,prerequisites=prerequisites,source_pins=source_pins,context_sha256=sha(a.context),
        compiler_sha256=c["compiler_sha256"],generic_dependencies=c["generic_dependencies"],
        controller_sha256=sha(Path(__file__)),application_object_banks_from_old_studies=[],
        repository=str(REPOSITORY),outputs_are_new_executions_only=True,
        expensive_full_clean_replay_executed=False,automatic_cleanup=False,
        original_numerical_inventory_preserved=True,
        compact_proof_only_derivation=dict(original_generated_modules=1020,derived_generated_modules=1022,
            unchanged_CSV_files=937,fresh_mathematical_provider_count=1035,
            original_typed_roots=29,diagnostic_import_probe_is_not_provider=True,
            modified_numeric_CSV_algorithm_or_claim=False),
        resources=dict(physical_owned_cgroup_bytes=300*2**30,host_reserve_bytes=256*2**30,
            independent_free_RAM_and_disk_for_heavy_stages=2**40,total_scratch_limit_bytes=300*2**30,
            scratch_stop_bytes=290*2**30,per_process_virtual_limits_are_not_RAM_commitments=True))
    atomic(a.run/"PLAN.json",plan)
    if not a.execute:
        print(json.dumps(dict(status=plan["status"],stages=stages,missing_public_interfaces=missing)));return
    runner=Runner(a);start=time.monotonic()
    try:
        need(not missing,"Pending public final controller/claim interface: "+json.dumps(missing))
        need(all(x["available"]for x in prerequisites),"An explicit executable/compiler prerequisite is unavailable: "+json.dumps(prerequisites))
        if set(stages)&PROTECTED:
            resource=load_module("rh080_owned_resources",PROJECT/"pv/supervise_resource_run.py").cgroup()
            need(resource.get("memory.max")==str(300*2**30)and resource.get("memory.swap.max")=="0",
                "Heavy execution requires its own300GiB/noSwap cgroup; use the documented user-service command")
            current=Path(resource["path"]).name
            if not a.unit:a.unit=current
            need(a.unit==current and a.unit.endswith(".service"),"Concrete owned service identity required")
        for name in stages:
            runner.run_stage(name);print("PASS new stage",name,flush=True)
        need(set(runner.completed)==set(stages),"Selected stage acceptance incomplete")
        for path,digest in source_pins.items():need(sha(Path(path))==digest,"Selected public execution source changed: "+path)
        atomic(a.run/"RESULT.json",dict(status="PASS_ALL_SELECTED_NEW_REPRODUCTION_STAGES",
            stages=runner.completed,commands=runner.commands,seconds=time.monotonic()-start,
            complete_campaign_reproduction=stages==ORDER,
            expensive_full_clean_replay_executed="n24-kernel"in runner.started_stages,
            expensive_full_clean_replay_completed="n24-kernel"in runner.completed,
            old_campaign_receipts_relabelled=False,automatic_cleanup=False))
    except BaseException as error:
        atomic(a.run/"INCOMPLETE.json",dict(status="INCOMPLETE_NO_WHOLE_CAMPAIGN_ACCEPTANCE",
            reason=type(error).__name__+": "+str(error),completed=runner.completed,
            commands=runner.commands,seconds=time.monotonic()-start,
            complete_campaign_reproduction=False,
            expensive_full_clean_replay_executed="n24-kernel"in runner.started_stages,
            expensive_full_clean_replay_completed="n24-kernel"in runner.completed))
        raise
if __name__=="__main__":main()
