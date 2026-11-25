# Strict-open populations between real consecutive cubes

Write \(N(a,b)=\#\{p\text{ prime}:a<p<b\}\). Each coefficient below gives a **strict** lower bound on \(N(n^3,(n+1)^3)/(n^2/\log n)\) for **every real** \(n\) in the indicated range.

| Bound | Range | Assumptions | Status |
|---|---|---|---|
| .70 | \(n\ge e^8\) | RH + inherited Green, Nicolas, BPT predicates | Inherited baseline, not a discovery |
| .8145 | \(n\ge2980\), in particular \(n\ge e^8\) | Exactly that inherited package | Written whole-cube octic derivation in wide.md, uses inherited moment caps |
| .788 / .802 | \(n\ge1250\) / \(n\ge2000\) | Same inherited package | Same written derivation, earlier onsets |
| .743 | \(n\ge e^8\) | RH + Schoenfeld predicate only | CubeSecondary.lean |
| .690 | \(n\ge1321\) | Same Schoenfeld package | CubeSecondary.lean |
| .9669 | \(n\ge400\), hence on the matched \(n\ge e^8\) ray | RH + Schoenfeld + Büthe (1.6),(1.7) | Secondary hybrid, CubeSecondary.lean |
| .988 | \(e^8\le n\le2154000\) | Büthe only | Finite slab, unconditional relative to that published computation |
| .9796 | \(n\ge1024\) | RH + Green + BPT + Büthe (1.6),(1.7); no Nicolas or Schoenfeld needed | Written trapezoidal hybrid, wide.md |

The .8145 row is a same-assumption improvement. It even strictly exceeds the **max** of the two inherited branches on \(n\ge e^8\): the normalized single-window branch is \((5.08985+1.4/\log n)\log n/\sqrt n \le 5.26485\cdot8/54.58<.772\), since \(\log n/\sqrt n\) decreases there. The strongest numerical row changes the assumptions. Written proofs are supplied for review, not claimed to have passed independent proof review or a full kernel check; see progress.md for receipts.

## Matched-scope comparison and exact sources

* Schoenfeld, *Math. Comp.* 30(134) (1976), Theorem 10 (6.1), p.337, proves the sharper \(\theta\) error with factor \((\log x-2)\log x\) under ordinary RH. The source is not itself a cube count. Its direct two-endpoint lower bound, normalized at \(n=e^8\), is below .75 (see wide.md and exact.py); later the same bound tends to 1 and exceeds the new octic coefficient. The mounted /corpus/literature/Schoenfeld1976.pdf is the recovered 1,795,864-byte original, SHA256 8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897, not the quarantined publisher response. The task's frozen facts describe the older unpinned state.
* Büthe, arXiv:1511.02032v2, p.2, Thm.2 (1.6),(1.7), is unconditional historical computation. Actual mounted PDF SHA256 350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1. Both theta predicates use \(p\le x\). The two hybrid components meet at \(n=2154000\); the exact cutoff permitted for the **right** cube is \(10^{19/3}-1\). We neither round that upward nor extrapolate. The underlying finite-domain bound is stronger than the uniform hybrid on much of its slab.
* Blanquer Robles v2 (21 Nov 2026), Theorem 2 (2), p.2 and §3 final paragraph p.10: for \(q=1\) ordinary RH suffices. The displayed affine widths for eventual short-window populations do **not** give an explicit complete-cube count at \(n=e^8\). The asymptotic count per unit width inferred by tiling from the displayed guarantees alone is at most \(1/1.505237<.665\) (one must preserve small width/count margins and allow removal of a right endpoint). This compares displayed lower bounds only, not the best retuning or actual primes. Theorem 3 gives right-closed existence from \(x=4\) and a quantitative right-closed count at fixed width coefficient \(c_*=.85125\) from \(x=4\cdot10^{18}\), not from \(e^{24}\). On its own count ray, the displayed finite count has efficiency \((\sigma+\beta\log(c_*t\log2/2)/t-\kappa/t)/(c_*M_W)<.09\) for \(t=\log x>42\): use \(c_*\log2/2<.3\), \(\log(.3t)/t\) decreasing there, and drop \(-\kappa\). Removing a possibly prime right endpoint cannot increase that guaranteed bound. These comparisons do not imply any global record.
* CMS v2 §6.3 (6.16) and Thms.3–5, and Blanquer Robles Thm.1, concern other scales and cannot be substituted for explicit cube populations. No retuning of \(A\), new Gaussian claim, or numerical onset for asymptotic gap conclusions.

## Boundaries and reproduction

Run /bin/lean CubeSecondary.lean and /bin/lean DualAudit.lean from this directory. Run /usr/bin/python3.10 exact.py for exact rational checks complementing the written proof. CubeDirect.lean transports baseline proofs to the local hypotheses needed for a whole cube; it is not by itself a completed kernel certificate for the written constants. build.py stages only assigned baseline sources. See progress.md for exact statuses.

DualAudit.lean imports CompactDualVerified and checks the unconditional L1-Fourier obstruction for actual Fourier pairs, fixed \(A=36/11\), with positive denominator. It separately checks the inherited V1 actual-C result under its compiler/runtime/uint64/ABI/hardware applicability boundaries. Neither is used to derive a cube count. No new C/C++/CUDA source-first PV, no fresh verification of Büthe's historical computation, no impossibility claim about other prime-gap methods, no RH proof.
