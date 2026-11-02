# Verified numerical FKS2 Table4-style transport

This is a new dedicated theta-to-pi application, not the earlier fixed nuAsympE30
program. Its source is c/fks2_table4_transport.c. It includes the original selected
sum.c body, a static30-element binary64 input array, exact2^-58rescaling, and three
upper-allowance additions. It calls no exp, log, Li or interval runtime.

The math is proved before the program is used: FKS2's partial-summation identity,
a bounded independent Table4 anchor at exp300,30whole-cell comparisons and a
whole-ray tail give the exact application allowance. The tail Q330/328 is a
proved conservative replacement for the sharper published maximum. The source
program's verified upper allowance is below5e-16, which implies Epi(x)<=5e-16 for
all x>=exp330. This is conditional on13named inherited CH2 premises and the
independent historical Table4 anchor. A separate pinned compatible replay
supplies the actual published OpenAI QRH proof. No enormous prime-counting value
is computed or assumed computable at exp300.

Reused unchanged from donor hs-chae/goldbach_pv, branch hs-chae/fp,
3b3205d18546726c51e3b832699a675e84a82aba: selected sum.c, allocated-array state/load
semantics, binary64/RN64 definitions and the general source-facing summation
stability theorem. The canonical donor overlay already exists in
Solutions/FKS2Numerics.v2. Restricted wrapper/static-array/call syntax,
source-token association, actual source execution, generalized binade rounding
certificates,30upward exp certificates, exact scaling, suffix error and mathematical
transport are NEW. Execution definitions contain arithmetic/source/state facts,
not an assumed accuracy field. The imported general stability theorem is an
actual dependency of the final computed upper allowance.

Build from this directory:

    lake update
    lake build Solution FKS2Table4.Replay FKS2Table4.Comparison

Canonical toolchain: Lean4.34.0-rc2, Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6.
The actual published QRH replay is separate under4.34.1/Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612;
no compiled objects cross compiler versions. Native finite facts use the existing
disclosed source-level trust tier, not official Comparator receipts. Generic
compiler/runtime/IEEE and the restricted constructor interpretation are trusted;
this is not a proof of arbitrary ISO C, GCC or hardware.

Existing Phase2 density pi bounds are stronger on this ray with extra
FKS-density/finite-RH inputs; Comparison.lean proves the displayed alternate
allowance is already below5e-16 throughout the ray. This experiment demonstrates
a genuine theory-to-program-verification-to-mathematics route, not optimality or
a strongest-current-network result. Original source/claims/receipts are preserved.
