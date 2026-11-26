# Whole FFT source-function contract

The complete original-grid recursive C norm functions now have a Lean source,
execution and arithmetic contract. This closes the earlier helper-only gap:
actual parameter binding, allocations, NULL checks, initialization, root and
twiddle construction, input loading, recursive FFT, unsigned magnitude sum,
rounding, coefficient quadrature, guarded answer, releases and return are all
consumed by one proof. Every permitted execution either returns the genuine
allocation-failure sentinel or the proved source-derived answer.

The generic theorem takes an independently kernel-proved mathematical FFT
certificate. It does not assume successful application execution, initialized
application state, observed output or application correctness. Instantiating
that certificate with a fixed literal numerical receipt and connecting the
result to the actual ANT consumer are separate final application obligations.
The generic contract alone is not a claim that either fixed ANT result has
completed owner-defined source-first PV.

## Preserved programs and inputs

- [Fap C source](fft/fap_fft_recursive.c): 131,072 FFT points, original
  400-node/m80 witness, exact original coefficient rescaling, allowance 20.
- [W4 C source](fft/w4_fft_recursive.c): 16,777,216 FFT points, original
  2,520-node/m360 witness, allowance 100.

These are the preserved recursive C alternatives. This proves their own
source semantics; it does not verify Python bytes or relabel the preserved
iterative port as verified. The numerical inputs, mathematical algorithms and
locked original caps are unchanged.

## Proof entry points

[FFTMainSourceNormProgram](lean/FFTMainSourceNormProgram.lean) packages the
independently proved complete-source syntax relation together with:

- `norm_call_exists`: constructs an actual complete norm-function Call from
  any well-scoped host caller, including the application's real initialization
  and its final lifetime and return-conversion steps.
- `every_norm_call`: classifies every actual Call as the real allocation
  sentinel or `normAnswer`; no suffix-correctness premise remains.
- `successful_norm_call`: every actual non-sentinel result equals that answer.

[FFTMainSourceNormSuffix](lean/FFTMainSourceNormSuffix.lean) proves the actual
38 source instructions after the four NULL checks, including all evaluation
orders. Its answer uses the exact certificate output's absolute-value sum,
transported from the actual C FFT output and actual source sum. The source
quadrature and upward divisions supply the remaining integer terms.

[FFTMainSourceNormAudit](lean/FFTMainSourceNormAudit.lean) checks ten typed
roots, the permitted three standard Lean axioms, and the proof dependency
links through all application stages and the all-execution failure classifier.
No native execution axiom or `sorry` occurs in these proof closures.

The construction is split into actual source stages, rather than an assumed
execution trace: `FFTMainSuffixFront` establishes instructions 8–21 from raw
calloc bytes, `FFTMainRecursiveStatement` proves instruction 22,
`FFTMainSuffixMiddle` establishes instructions 23–35, and
`FFTMainFinishTotal` establishes instructions 36–45.

## Reproduce

Use the compiler and exact dependency commits in [DEPENDENCIES.json](DEPENDENCIES.json)
and the context creation instructions in [README.md](README.md#reproduce).
From this directory:

```sh
python3 make_context.py --compiler /toolchain/bin/lean --mathlib /path/mathlib \
  --output /absolute/fresh/clean_proof_context.json
python3 reproduce_lean.py --context /absolute/fresh/clean_proof_context.json \
  --root FFTMainSourceNormAudit --run /absolute/fresh/main-source-cold
python3 reproduce_recursive_physical.py --program all --mode all \
  --run /absolute/fresh/physical-observations
```

The source-cold command regenerates the entire selected application proof
closure from generic dependencies. The physical command compiles and executes
the actual unchanged C programs and records exact source/compiler/binary hashes,
commands, stdout, resources and strict results. Physical observations remain
separate evidence; they are not a Lean execution axiom. No random seed is used.

The completed composition receipt is a source-associated replay, not a new
whole-cone source-cold replay. It rebuilt 18 modules against 465 precisely
validated dependencies in 49.39 seconds. The final combined source-cold replay
and fixed literal-certificate/ANT instantiations must be checked separately.

## Remaining trust boundary

The source fragment's independently specified syntax, typed application
execution, array bounds, arithmetic overflow/casts, real loop initialization,
helper applicability, lifetimes and numerical-model correspondence are proved
in Lean. They are not delegated to a platform contract.

The documented generic compiler, core runtime, ABI, operating-system, C memory
and I/O API, and hardware correctness remain trusted when associating an actual
compiled run with that execution model. The memory contract precisely permits
calloc failure or a fresh zeroed byte allocation and specifies free release;
it supplies no initialized application representation or correct answer.
The stdout harness records physical observations under that boundary. Semantic
adequacy of this chosen C model for the trusted compiler/ABI remains a disclosed
boundary, distinct from proved source-to-AST syntactic correspondence.
