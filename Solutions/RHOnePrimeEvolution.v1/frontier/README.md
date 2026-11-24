# Prime-index and Goldbach frontier

This folder contains new consumers of the frozen octic population proof. It does not claim a new Fourier kernel or a global literature record. No Ramanujan work is included.

The main new arithmetic result is a range/multiplicity tradeoff for actual sorted ternary Goldbach representations. The old injection selected primes above n/2, so it required n>2H when the binary Goldbach input was verified up to H. A selected prime above n/3 can be one of at most two large components of a sorted triple. With no size restriction, at most three components are possible. The resulting lower counts are the old rich count divided by one, two or three according to the exact n/H range. The original no-loss branch is retained.

A completely explicit corollary proves more than750 million sorted triples for every odd n from6×10¹⁸ through8×10¹⁸, conditional on the same RH/general literature inputs and finite binary Goldbach up to4×10¹⁸. The entire band was outside the old n>8×10¹⁸ geometry. This does not newly prove the finite binary input.

The prime-index consumer uses zero-indexed Nat.nth: the index primeCounting(floor x)+m is the(m+1)st prime above x. It preserves both strict interval endpoints. Inverting the whole count margin yields an x-dependent width, clamped to the actual supported domain[1.03,16]. It also retains the stronger specialized2.15 branch; the generic family has a smaller logarithmic margin at that same width and cannot replace it.

The finite-gap bridge brackets every real x by genuine consecutive primes using finite min/max operations, then transfers a standard finite gap contract to a strict-open prime interval. Its historical gap input remains explicit; the terminal primality proof is supplied separately. Numerical kernel proofs are not source-first PV.

Read THEOREMS.json for exact domains and SOURCES.json for the primary comparator locator. The exact crossing of the displayed octic and Chirre curves is10033/29152. The published curve is an asymptotic infimum upper bound, not an optimum. At equality of the octic width curve the finite count is strictly above the target; a strict limiting margin needs a positive additional allowance.

## Incremental reproduction

Run reproduce.py with --context naming the pinned compiler/generic-libraries JSON, --proof-bank naming the accepted frozen octic union, and --out naming a NEW experiment-owned output directory. The script snapshots executed sources, compiles them with Lean4.34.0-rc2 under64GiB address-space caps, saves exact commands/stdout/GNU-time/hash evidence, and runs the actual proof-value/axiom audit. Use --modules FiniteGapBridge for the independent finite transfer alone. This incremental frontdoor reuses historical application proof objects and does not claim a fresh transitive rebuild. The campaign-level clean composition and primary-source audit remain separate gates.
