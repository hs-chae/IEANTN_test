#!/usr/bin/env python3
"""Source-cold developer replay, not an IEANTN Comparator receipt.

Supply a pinned context JSON with compiler and generic_lean_path fields.
Only generic Mathlib/dependency libraries may occur in generic_lean_path.
Every local proof library below is compiled from source into a fresh output.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

MODULES = [
    "ExplicitAffineWindow", "ExplicitSignedLogMoment", "ExplicitHatIntegrals",
    "ExplicitCosineMoment", "ExplicitAffineIntegrals", "ExplicitNodalMoments",
    "ExplicitHatFourier", "ExplicitAffineFourier", "ExplicitFiniteDifference",
    "ExplicitAffineSignedMoment", "ExplicitFourierPair", "ExplicitCMSEligible",
    "ExplicitDomain", "ExplicitWindowErrors", "ExplicitBRStripTransfer",
    "ExplicitGWTestFunction", "ExplicitGuinandWeilApplication", "ExplicitMellinFourier",
    "ExplicitNormSourceBridge", "ExplicitEntireUniqueness", "ExplicitCompactLaplace",
    "ExplicitMellinArithmetic", "ExplicitMellinPoles", "ExplicitDigammaDifference",
    "ExplicitDigammaFubini", "ExplicitGammaFourier", "ExplicitGammaAffine",
    "ExplicitGammaSubstitution", "ExplicitSecondPoleIntegral",
    "ExplicitMellinGammaCancellation", "ExplicitMellinIdentity", "ExplicitRHMellin",
    "ExplicitBRPopulationConsumer", "ExplicitPoleError", "ExplicitPoleQuantitative",
    "ExplicitAffineDerivative", "ExplicitDerivativeIntegrals", "ExplicitRealZetaNonzero",
    "ExplicitCMSZeroSource", "ExplicitZeroRemainderIntegrals", "AffineDerivativeBounds",
    "ExplicitAffineZeroRemainder", "ExplicitMellinZeroBound", "ExplicitTruncatedLogDensity",
    "ExplicitZeroBoundary", "ExplicitAffineZeroAdmissible", "ExplicitAffineZeroEstimate",
    "ExplicitZeroAllowance", "ExplicitPrimePowerAllowance", "ExplicitTrivialError",
    "ExplicitResidual", "ExplicitCMSZeroRoot", "ExplicitMellinLower",
    "ExplicitDiscreteBV", "ExplicitAtomicBV", "ExplicitMontgomeryVaughan",
    "ExplicitMVAtomic", "ExplicitAudit",
    "ExplicitPrimeWeights", "ExplicitMVConstants", "ExplicitCentralPrimes",
    "ExplicitErrorBudget", "ExplicitAnalyticTransfer", "ExplicitScalarLogBounds",
    "ExplicitProfileScalars", "ExplicitProfileResiduals",
    "AffineCellInterpolation", "AffinePositiveCellArea", "AffinePopulationBounds",
    "AffineLipschitz", "AffinePositiveVariation", "AffineWingBV",
    "PrimePowerWindowBounds", "ActualPrimePowerAllowance", "ActualPrimeWings", "ActualArithmeticSplit",
    "ExplicitAsymptoticWidth", "ExplicitAsymptoticAllowances", "ExplicitAsymptoticCentral",
    "ExplicitActualPopulation", "ExplicitFinalAnalyticAudit",
]
AUDITED = [
    "signed_log_affine_inverse_three_eighths", "fourier_affine_inverse_eq_window",
    "affine_inverse_eligible", "integral_sq_abs_affineSpectrum_le",
    "inverseCosine_affineSpectrum_variation_bound", "support_lower_geometry",
    "affine_strip_extension_by_mesh_dilation", "mellin_test_function_strip",
    "guinand_weil_affine_test", "fourier_mellin_extension",
    "affine_norm_eq_periodic_by_padding", "poleScale_lower",
    "log_inverse_halfLogWidth_upper", "entire_extension_eq_compactLaplace",
    "mellinTest_imaginary_value", "digammaDifference_integral",
    "gamma_affine_frequency_integral", "affine_mellin_identity",
    "source_RH_affine_mellin_identity", "source_BR_population_goodCoefficient",
    "windowLaplaceIntegral_error", "mellin_pole_lower",
    "actual_mellin_pole_lower_domain", "derivative_halfline_envelopes",
    "hasDerivAt_inverseCosine_affineSpectrum", "inverseCosine_affineSpectrum_deriv_bound",
    "real_zeta_ne_zero", "cms_full_zero_bound_from_sources",
    "zero_remainder_integral_le",
    "mellin_zero_norm_bound",
    "affine_zero_remainder_normalized_le",
    "truncated_log_density_le",
    "zero_main_boundary_tendsto",
    "zero_remainder_boundary_tendsto",
    "affine_CMSZeroAdmissible",
    "affine_zero_estimate",
    "zero_allowance_lt",
    "affine_zero_estimate_domain",
    "primepower_window_allowance_lt",
    "trivial_integral_bound_domain",
    "explicitResidual_slab_lower",
    "explicitResidual_monotone_ray",
    "count_gt_one_of_residual",
    "cms_zero_count_root_exists",
    "actual_mangoldt_lower",
    "finite_atomic_continuous_BV_bound",
    "mv_interval_entrance_bound",
    "mv_log_coordinate_prefix_bound",
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--context", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True,
                    help="new experiment-owned output directory; must not exist")
    ap.add_argument("--memory-gib", type=int, default=32)
    args = ap.parse_args()
    if not 1 <= args.memory_gib <= 300:
        raise SystemExit("memory limit must be within authorized 1..300 GiB")
    context = json.loads(args.context.read_text())
    compiler = Path(context["compiler"]).resolve(strict=True)
    generic = context["generic_lean_path"]
    for entry in generic.split(":"):
        if not entry or not Path(entry).is_dir():
            raise SystemExit("missing generic dependency path: " + entry)
    source = Path(__file__).resolve().parent
    repo = source.parents[2]
    vocabulary = repo / "IEANTN/Vocabulary/CMSFunctional.lean"
    zeta_vocabulary = repo / "IEANTN/Vocabulary/Zeta.lean"
    def module_source(name):
        candidates = [source / (name + ".lean"), source.parent / "primal" / (name + ".lean")]
        matches = [p for p in candidates if p.is_file()]
        if len(matches) != 1:
            raise SystemExit("missing or ambiguous selected proof source: " + name)
        return matches[0]
    ordered = []
    visited = set()
    active = set()
    def visit(name):
        if name in visited:
            return
        if name in active:
            raise SystemExit("selected proof import cycle: " + name)
        active.add(name)
        for line in module_source(name).read_text().splitlines():
            if line.startswith("import "):
                for dep in line[7:].split("--",1)[0].split():
                    if dep in MODULES:
                        visit(dep)
        active.remove(name)
        visited.add(name)
        ordered.append(name)
    for name in MODULES:
        visit(name)
    proof_sources = [vocabulary, zeta_vocabulary] + [module_source(m) for m in ordered]
    forbidden = re.compile(r"\b(?:sorry|native_decide)\b|(?m:^\s*axiom\b)|Lean\.ofReduceBool|implemented_by")
    for path in proof_sources:
        if forbidden.search(path.read_text()):
            raise SystemExit("forbidden proof construct: " + str(path))
    args.out.mkdir(parents=True, exist_ok=False)
    objects = args.out / "objects"
    logs = args.out / "logs"
    objects.mkdir()
    logs.mkdir()
    frozen = args.out / "frozen-source"
    for path in proof_sources:
        target_source = frozen / path.relative_to(repo)
        target_source.parent.mkdir(parents=True, exist_ok=True)
        target_source.write_bytes(path.read_bytes())
    (frozen / "reproduce.py").write_bytes(Path(__file__).read_bytes())
    env = dict(os.environ, LEAN_PATH=str(objects) + ":" + generic)
    compiler_version = subprocess.run([str(compiler), "--version"], check=True,
        capture_output=True, text=True).stdout.strip()
    jobs = [("IEANTN.Vocabulary.CMSFunctional", frozen / vocabulary.relative_to(repo), frozen),
            ("IEANTN.Vocabulary.Zeta", frozen / zeta_vocabulary.relative_to(repo), frozen)]
    jobs += [(m, frozen / module_source(m).relative_to(repo),
              frozen / module_source(m).parent.relative_to(repo)) for m in ordered]
    rows = []
    began = time.monotonic()
    for module, path, root in jobs:
        target = objects.joinpath(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        usage = logs / (module + ".time")
        command = ["/usr/bin/time", "-v", "-o", str(usage), "prlimit",
            "--as=" + str(args.memory_gib * 2**30), "--", str(compiler), "-j2",
            "-R", str(root), "-o", str(target), str(path)]
        started = time.monotonic()
        run = subprocess.run(command, env=env, capture_output=True, text=True)
        stdout = logs / (module + ".stdout")
        stderr = logs / (module + ".stderr")
        stdout.write_text(run.stdout)
        stderr.write_text(run.stderr)
        row = dict(module=module, source=str(path.relative_to(frozen)),
                   source_sha256=sha(path), exit=run.returncode,
                   seconds=time.monotonic()-started, command=command,
                   stdout_sha256=sha(stdout), stderr_sha256=sha(stderr),
                   usage_sha256=sha(usage))
        text = usage.read_text()
        found = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
        row["peak_rss_kib"] = int(found.group(1)) if found else None
        row["oom_observed"] = run.returncode in (-9, 137)
        if run.returncode:
            rows.append(row)
            (args.out / "FAILED.json").write_text(json.dumps(rows, indent=2) + "\n")
            sys.stderr.write(run.stdout[-8000:] + run.stderr[-2000:])
            return 1
        row["object_sha256"] = sha(target)
        rows.append(row)
        print(module + " PASS", flush=True)
    audit = (logs / "ExplicitAudit.stdout").read_text()
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in AUDITED:
        pattern = r"'RH080Next\.Explicit\." + re.escape(name) + r"' depends on axioms: \[([^]]*)\]"
        found = re.search(pattern, audit, re.S)
        if not found:
            raise SystemExit("missing axiom audit for " + name)
        actual = {x.strip() for x in found.group(1).split(",") if x.strip()}
        if not actual <= allowed:
            raise SystemExit("unexpected theorem axiom: " + repr(actual-allowed))
    final_audit = (logs / "ExplicitFinalAnalyticAudit.stdout").read_text()
    final_names = re.findall(r"^#print axioms (\S+)", module_source("ExplicitFinalAnalyticAudit").read_text(), re.M)
    for qualified in final_names:
        found = re.search(r"'"+re.escape(qualified)+r"' depends on axioms: \[([^]]*)\]", final_audit, re.S)
        if not found:
            raise SystemExit("missing final analytic audit: " + qualified)
        actual = {x.strip() for x in found.group(1).split(",") if x.strip()}
        if not actual <= allowed:
            raise SystemExit("unexpected final analytic theorem axiom: " + repr(actual-allowed))
    result = dict(kind="source-cold developer proof replay; not a Comparator receipt",
                  status="PASS", compiler=compiler_version, compiler_sha256=sha(compiler),
                  generic_lean_path=generic, context_sha256=sha(args.context),
                  source_manifest=rows, audited_theorems=AUDITED+final_names,
                  permitted_axioms=sorted(allowed), seconds=time.monotonic()-began,
                  output_bytes=sum(p.stat().st_size for p in args.out.rglob("*") if p.is_file()),
                  scope="source-cold complete generic actual affine Fourier/Gamma/Mellin/zero/pole/trivial, actual primepowers/MV/arithmetic, continuous fixed-profile residuals and strict prime consumers, plus arbitrary-c actual-pi population transfer; fixed-input C source providers are separately reproduced and original-profile FFT norm verification remains open")
    temp = args.out / "RESULT.json.tmp"
    temp.write_text(json.dumps(result, indent=2) + "\n")
    temp.replace(args.out / "RESULT.json")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
