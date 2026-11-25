# PrimeInterval.v5

`Solution.lean` imports the proved finite-frontier adapter. It implements all four canonical challenges with their actual typed historical source inputs: terminal closed1550, terminal strict1550+epsilon, strict logarithmic-square width, and their strict minimum.

The complete clean source-only reproduction and evidence are in `Solutions/RH080Study.v1/finite_frontier/`. Historical prime-gap computations remain explicit B-tier inputs; terminal primality and all finite transfers are kernel proved. No RH or source-first PV is asserted. The terminal range excludes x=18446744073709551557 and does not cover all x below2^64. Official Comparator approval is separate from the local Lean build.
