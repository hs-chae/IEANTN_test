# Actual octic Fourier moments from complete kernel certificates

`OcticCertifiedMoments.lean` proves the actual half-line Fourier moments at most
5.72 and4.6. `OcticStrongMomentCaps.lean` preserves those theorems and proves
**M0 <=5.7184** and **M1 <=4.576**, with no numerical premise. The exact function
is the Fourier transform of `(1-u^8)` on[-1,1], not the fourth power of(1-u^2).
`SOURCE_ROOTS.json` freezes all128 module/file/hash identities. Every new final
root uses only standard Lean axioms, with no native-execution axiom or sorry.
These are ordinary kernel numerical certificates, **not source-first PV**.

`ENDPOINT_RESULTS.json` describes the exact statements, parameters, trust labels,
results and resources. `evidence/development/` preserves every module's compiler
receipt and stdout/stderr. These development builds reuse application banks;
that is explicitly distinct from the final cold source-only supplemental replay.

## Clean reproduction

Install the exact compiler/generic dependency revisions and local context paths
in `Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json`. Keep the compiler
SHA and dependency revisions fixed. From the network root:

```sh
python3 Solutions/RHOcticPush.v1/integration/corrected/reproduce.py --out /fresh/primary
python3 Solutions/RHOcticPush.v1/integration/supplement/reproduce.py --primary /fresh/primary --out /fresh/supplement --jobs 8 --memory-gib 64
```

The second controller is maintained by the integration workstream. It checks the
complete current-campaign primary source/object/C proof closure, then rebuilds
all supplemental sources and final consumers. Its final receipt, once accepted,
is separate from this folder's development evidence. No DEV object bank is a
permitted substitute for the cold source replay. Parallel numerical leaves are
independent; their declared imports must already be source-built.

To regenerate the deterministic proposals and exact proof texts, install
`mpmath==1.3.0` and run:

```sh
python3 Solutions/RHOcticPush.v1/moments/endpoint/generate_endpoints.py --check
python3 Solutions/RHOcticPush.v1/moments/endpoint/generate_logs.py --check
python3 Solutions/RHOcticPush.v1/moments/endpoint/generate_cells.py --check
python3 Solutions/RHOcticPush.v1/moments/endpoint/generate_blocks.py --check
python3 Solutions/RHOcticPush.v1/moments/endpoint/generate_assembly.py --check
```

Omit `--check` only in a fresh reproduction copy to regenerate those files.
Proposals use100decimaldigits and no random seed. Neither mpmath nor native
feasibility diagnostics are trusted as mathematical evidence. Every one of the
7301 Fourier endpoints,7301 log endpoints and7300 rounded cell inequalities is
recomputed by `decide +kernel` in115 complete proof blocks. The full integer cell
sum totals are also kernel proved. Final real-interval and infinite-tail bounds
consume the analytic quadrature/assembly theorems, rather than extending finite
samples to a continuum.

## Numerical algorithm and its proved meaning

The old core trigonometric evaluator uses a floor period shift, then a coarse
[-1,1] fallback when the shifted point exceeds4. This conservatively rejects
some tight endpoint proposals. The new private checker rounds to a centered
period and directly reuses the existing verified Taylor enclosures at depth20.
Its general proof works for **any chosen integer period**, via interval membership
and exact sine/cosine periodicity. Soundness does not assume the period heuristic
is correct. Original LeanCert files and the primary study remain unchanged.

The mesh is0..10 by0.01,10..100 by0.05, and100..1000 by0.2. Endpoint proposals
include radius1e-4/(1+q), then round upward at1e-8; logarithms round upward at1e-8.
Cells round upward at1e-12. Their exact integer totals are5702265466890 and
6165186432541 with denominator1e12. The signed negative[0,1] logarithmic moment is
retained with proved bound-170/99. The entire infinite tail is paid with16113/1e6
and the corresponding(log1000+1) logarithmic factor. Zero is treated by the exact
proved mass16/9; the actual positive-log consumer uses only arguments at least1.

## Resources and preserved evidence

The115-block phase completed in792.39seconds using8 admitted compiler lanes.
Its **largest individual child** peak RSS was9.78GiB. Aggregate process-tree peak
RSS was not sampled in that development run and is not inferred by multiplying
child maxima. Each child had a64GiB address-space ceiling; actual initial RAM and
independent free disk admission are retained in the batch resource record.
The batch's final owned output size was1,422,099bytes, not a measured intra-run
high-water mark. All115 accepted compiler invocations returned0; this is not an
attribution of global host OOM counters. Fresh supplemental replay separately
records its own resources, source closure and execution receipts.

The first overly tight endpoint proposals and all failed proof/validator attempts
are retained under `attempts/` and `ATTEMPTS.md`. Original data, programs, sources,
results and accepted proof artifacts were not deleted or overwritten. Generated
tables and block sources are small; no large regenerable scratch was produced.
The original long-running high-count workers belong to another study and were
left untouched.
