# Agent A numerical winner search — partial result

This isolated solution verifies a finite numerical subproblem. It does **not** establish an improved prime-number-theorem envelope. No node is registered and no official receipt is created.

`WinnerProgramA/Program.lean` is the actual exact interval executable, not a C model or a returned precomputed coefficient. It constructs expression operands, evaluates every cell with the inherited domain-checked dyadic interval engine, and checks separately proposed rational bounds. `Exec` is evaluation equality and contains no accuracy or desired-result premise. Generic upper/lower soundness consumes that execution and the computed acceptance. `Semantics.lean` proves that its moment syntax denotes the written Taylor-four expression.

`Certificate.lean` reconstructs the independent report's17,500cell right-rectangle expression P0 and a2,800cell weighted-chord expression P1 using the same table constants. It checks P1 from above and P0 from below, including the low-zero/truncation remainder. The intended inequalities are P1<=.012833<.0128577<=P0. The two concrete Boolean checks use `native_decide`; generic soundness uses only standard Lean axioms. This is not a three-axiom-only concrete result.

The incumbent competition includes the exact incomplete-gamma moment in FKS Lemma2.5, which already beats the finite Taylor-four quadrature. Thus the numerical improvement cannot establish an actual envelope win. The complete density/layercake/height/whole-ray prime-counting consumer is not newly formalized here. A warm-start count-window idea remains diagnostic, with original density-parameter comparison pending.

## Run

Use canonical Lean4.34.0-rc2, Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6. From this directory, `lake update && lake build` builds the solution; `lake exe winner-program old` and `lake exe winner-program new` evaluate the programs and print computed row intervals. Internet/cache setup may be needed. Do not mix in the separate4.34.1 actual-QRH objects.

The recorded fresh compilation used the same-pin inherited source libraries in a disclosed local cache; see the portable evidence helper and logs in the companion bundle. This is not a cold dependency replay or an official Comparator run. The baseline is reconstructed from report equations, not the original authors' program. Discovery and implementation were retrospective. No push/PR is authorized.
