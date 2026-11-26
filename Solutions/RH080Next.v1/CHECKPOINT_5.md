# Checkpoint5: full-main finite source-first consumers

The actual C sources are unchanged. `pv/lean/FFTFapMainNumerics.lean` consumes
`MainIO.Result`, which contains an actual complete operational main Call, its
logical stdout and last successful printf event. The output value is derived
by `MainIO.result_value_eq` from the universal actual-main theorem, not a
separate certificate observation. All application allocation, initialization,
recursive FFT, fixed-point arithmetic, normalization, output cast and main
control flow are proved. Generic allocation failure returns the real sentinel;
printf can return a negative int after a prefix, and the preserved source still
returns0. Physical buffering/flush/OS delivery remains a generic platform boundary.

`FFTFapMainConsumers` proves exactly the original strict bounds:0.8 on
4≤x≤exp174,0.74 on11≤x≤exp63, and0.75 on11≤x≤exp70. Named RH, BR Fourier,
CMS explicit-formula/zero-count, DLMF, Montgomery–Vaughan and historical finite
gap inputs remain explicit. The generalized zero-transfer scheme is eliminated
by `ExplicitCMSZeroKernel.cms_zero_partial_summation_kernel`.

`FFTFapMainAudit` checks all3 exact final types, standard axioms only, and actual
proof dependencies through full main/printf, numerical FFT/quadrature and the
new generic zero theorem. Its accepted batch contains3 fresh modules and669
exact source-associated dependencies,52.54s. The separate491-module generic
source-cold replay took1032.51s, max compiler RSS39,568,330,752bytes; sampled
group memory79,113,412,608bytes is a lower bound on the aggregate peak.
Zero observed OOM events there were captured before its owned cgroup disappeared;
no fabricated final cgroup readback is used. Zero/kernel canonical cold proofs
and exact resource records are preserved separately in evidence.

The24 unchanged compiled C runs (both profiles×O0/O2/O3/UBSan×Python
normal/-O/-OO) matched exact outputs. They corroborate the modeled program;
execution observations alone are not source-first PV. No retained completed
cgroup OOM counter exists for those runs; exact per-run time/RSS/logs do.

This checkpoint does not claim full campaign completion: W4 N24, final global
consumers, final canonical sealing, supplemental13 exact-payload reviews and
one complete offline report/bundle remain pending. Original20+8 trial results
and16 new primary statuses are immutable. New study data are separate,
posthoc-selected prospective transfer experiments, with no general causal claim.

The machine-readable reviewed file inventory is `CHECKPOINT_5_FILES.json`.
Historical absolute paths in receipts identify executed environments; portable
source-only commands are in `pv/MAIN_SOURCE_COLD_REPRODUCTION.md`. New canonical
WIP and the uncompiled W4 final leaf are deliberately excluded from this push.
