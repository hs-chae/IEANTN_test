# Phase V — unchanged numerical computations

Status: completed fixed-program proof/consumer replays, actual-root audit, 180 spectral controls and 110 forward controls in all five Python modes. All selected numerical outputs were already verified in the starting snapshot. This phase demonstrates honest reuse and replay, not first-time verification or a numerical improvement.

## Frozen computation identities

The spectral program remains `Configuration.program 1 = Separated.program 330 100 65536`: two rows, 65,536 strip cells plus the one-cell base row, precision -100 and Taylor depth 32. Its exact row caps remain `[3/10^12,9150520019/10^12]`; their sum is `9150520022/10^12`. The source-to-AST identity, execution test, generic enclosure soundness and real-valued coefficient semantics are unchanged. The full π consumer retains every old ray and its pointwise minimum.

The second selected numerical family is the already-frozen Ramanujan C program in `Solutions/RamanujanNumerics.v2/c/updated.c`. “Updated” is its historical name: it belongs to F in Experiment 1. Its seven literal inputs, scale 4096, offsets 134 and 119, ten floating-point operations, output bits `4022338dd9402a60` and advertised cap `9101/1000` are unchanged. Fresh Lean elaboration checks the literal enclosures, input domain, source/AST match, execution witness, IEEE suffix and forward error budget. The supplied certificate is used by the actual epsilon provider and Ramanujan loss/gap consumer.

The four Gaussian full-integral caps also remain fixed: `3550829/10^6`, `882173/250000`, `877061/250000` and `3471693/10^6`. `WinnerHeightProfiles.profile_J_upper` was freshly replayed as a real integral consumer of the existing signed-kernel certificates. Its eight finite native facts were reused, not recomputed or relabeled as new evidence.

## What was freshly checked

`ForwardRamanujanUpdate.Updated`, its Provider/Input/Consumer/Assembly chain, `PVEvolutionA.Result`, `PVEvolutionA.Pointwise`, and `HeightKernelPackage` passed fresh targeted source elaboration. Two unchanged core statement modules were also re-elaborated into the private object directory; no core source, statement, designation, fingerprint or official receipt was edited.

The actual-root audit passed for:

- `PVEvolutionA.pi_best`: 51 inherited finite native axioms.
- `WinnerHeightProfiles.profile_J_upper`: 8 inherited finite native axioms.
- `ForwardRamanujan.Updated.certified_upper`: 6 finite native axioms, freshly reevaluated with the same old inputs.
- `ForwardRamanujan.forward`: 12 inherited finite native axioms, including both old program proofs.

The audit uses unpruned `collectAxioms`, identifies each native owner and its mathematical type, verifies non-vacuous displayed inputs, and checks actual source/execution/soundness/consumer edges. There is no sorry or unreviewed custom axiom. Foundational Mathlib/runtime bodies are pinned leaves in the separate project-body traversal.

The unchanged spectral gate passed 180 fresh actual-CLI controls: 36 cases in all five Python modes. Every valid run checks all three frozen routes. The cases cover the 27 actual native owners, wrong inputs, partitions and caps, coherent rehashing, duplicate JSON, NaN, overflow and a Boolean schema. Rejected runs issue no accepted receipt. The gate protects 2,708 historical source/evidence files; its numerical-source identity is `24cedf7f764357d18954c277ee2bd19b1b7f10e0a9820645bae9391e28871910`.

The unchanged forward gate checks all nine original active routes and 5,033 source/evidence files. Its fresh mutation matrix is recorded separately in `evidence/V/FORWARD_CONTROLS.json`. These validators check recorded source/evidence association; fresh Lean proof replay is separate evidence. Their old `noPV_comparison=PENDING` field is historical and does not replace Experiment 1's completed N checkpoint.

Four actual C compiler diagnostics passed: both fixed old and frozen-updated sources at O0/O2, with fast-math and contraction disabled. The binary64 environment preflight and output bits agree with the corresponding exact Lean source. These are host/compiler diagnostics, not a formal proof of the C compiler or hardware.

## Expensive duplicate and cache recovery

A fresh duplicate of the 65,536-cell numerical proof was started before its historical runtime was inspected. Its recorded original canonical run took 6,571.355 seconds. The duplicate was stopped at 356.824 seconds and about 4.35 GiB peak RSS; its FAIL/SIGTERM record and source/log remain. It supplies no new certificate. The exact source and existing verified object match the frozen historical source/record instead. This is evidence reuse, not a completed cold replay of that large computation.

Private cache recovery first needed the correct application `srcDir` mapping for FKS2SumBridge/FKS2Scalar/SumStability, and a complete core namespace overlay. Missing-prefix failures were retained; they were not interpreted as source absence or mathematical failure. The successful smaller program and consumers use source-identical, same-pin inherited objects plus freshly elaborated owned targets. There was no cold mass build and no cross-compiler object reuse.

## Unchanged mathematics and assumptions

The V pools retain all N analytic improvements and old numerical facts. Their mathematical envelopes are the same: ΔV=0. The new direct weighted argument and sharpened remainder were already proved in N, so they are not credited to program verification.

The π root retains its explicit CHJ-I, zero-count, first-zero, PrimaryInputs8, finite-RH and QRH assumptions. The fixed Ramanujan assembly retains its original `QRHCH2.v5.psi_refined_bound` argument: for every real x≥exp(300), genuine Eψ is at most `(log x)^2*x^(-1/8)/566`. Its loss allowance is `9.101/log x` for x>exp(3915); the real gap lower bound is the corresponding old conclusion. This does not improve the already-existing Boolean Ramanujan cutoff exp(145) under its additional inputs.

No new calibration, input array, partition, precision policy, numerical cap or consumer target was introduced. Native-assisted research evidence remains outside official standard-axioms-only Comparator acceptance. Compiler/runtime/hardware contracts remain trusted. No push, PR or official dispatch occurred.

## Transition to E

After this immutable V checkpoint, genuinely changed numerical instances may be admitted only with the existing source-linked verification gate and actual consumer proofs. Numerical changes and analytic changes will be recorded separately. The starting N functions and every legacy route remain in the cumulative comparison pool.
