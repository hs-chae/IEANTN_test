# Canonically certified prime base and exact original million-bit mask

The new generic theorem PackedSievePrimeBase.primitive_eq_original proves that OR-ing divisor masks over a list has exactly the old primeBits output, provided its list bitmap equals the canonical small primeBits(2,r−1) bitmap and its entries lie between2 andr. Least-prime-divisor completeness proves the reverse direction. No primality table is assumed.

The ground base r=195856 is CLOSED: the17,642-entry proposed list has kernel-checked bounds and a kernel equality against the canonical195,855-bit base mask. The canonical base itself uses the existing correct small sieve; no per-prime Lucas cascade is imported. The million-window result is CLOSED for lo38358837684,count1000000. All outputs are exactly the unchanged original P mask.

A correction to the motivation matters: the OLD compositeMask already skips composite divisors using unmarked bits of allMask2r. It does not OR all195,855 divisors into the final mask. The new method folds the certified explicit17,642-entry list directly, removing195,855 conditional/testBit iterations. Its smaller canonical base also filters its own small divisors. This is a kernel numerical-provider optimization, not a new native C bitset program, C-program speedup or stronger ANT claim.

Actual same-host component profiles,48GiB caps: fresh old algorithm with precompiled original literal110.482s; certified-list algorithm with the SAME precompiled literal77.762s; canonical-base certification22.713s. Base+newmask100.474s is the SUM of separate phases, not one uninterrupted cold measurement. The combined certified-list+standalone4096-bit DATA proof took78.534s; DATA preparation4.535s and base certification are separate. Original standalone literal DATA preparation took26.127s. RESULT.json includes each exact stage, complete CPU/RSS and stage sums. No statistical confidence or optimality claim is made. No failed Lean attempt or OS OOM occurred in this scout. Six intentional CLI guard rejections are not negative mathematical evidence.

Two independent compiled audits cover the actual proof/type closures. Combined equality6086constants/standard3; its numeric computation448constants/propext. All closed base/range/minFac/canonical/codec paths are required. The actual10721 imported modules contain no baseline P/Q mask module, calibration/provider Equality, Lucas or old local-primality provider. Neither old P equality theorem occurs on the new proof paths. The combined equality has no external theorem premise. The parent integration packet separately consumes this output through the unchanged source-verified C program and proves the SAME original real interval and501901 margin; this component itself is not source-first PV.

## Deterministic generation

From the matching published solution directory:

```sh
python3 scripts/generate_prime_base_mask_scout.py --out /absolute/FRESH_BASE
python3 scripts/generate_balanced_mask_data.py \
  --baseline-source evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean \
  --out /absolute/FRESH_DATA --data-only-4096 --provider-check
```

The first generator recreates all four accepted source files byte-for-byte, including the list and closed canonical-base proof. The second recreates the standalone balanced4096 DATA. Both generators are untrusted proposers; only the compiled kernel proofs validate the mathematical outputs. Source-only regeneration passed under normal Python,-O,-OO with identical numerical source hashes. There is no random seed.

## Fresh kernel reproduction

Use the pinned compiler/dependency commits in BUILD_CONTEXT.json and matching repository source. The complete executable script scripts/reproduce_prime_base_mask_scout.sh accepts SOLUTION,PINNED_CONTEXT,FRESH_OWNED_OUT,CPU_CSV. It regenerates both source populations and invokes the FROZEN guarded source-closure helper on PackedSievePrimeBaseCombinedAudit with fresh application objects, two48GiB workers,96GiB aggregate and512GiB host reserve. It then runs the actual completed-result reader under-OO. All generated output must be new and inside the existing whole experiment scratch root. Genuine1TiB available RAM and independently1TiB free disk/300GiB total scratch guards apply. Read the script's prerequisites before execution.

The recipe has been syntax-checked and its source-generation routes have actually passed; the full fresh dependency-closure/kernel replay was NOT executed in this bounded scout. Recorded seven mathematical/audit compiles used existing pinned framework objects and fresh new modules. The supplied generic source, all four generated sources, standalone DATA source, original untrusted proposal input, exact parameters, compiler/context pins, commands, accepted receipts, stdout/stderr/rusage and cryptographic hashes are preserved here. No D-only source dependency is required for regeneration. The parent combined-consumer reproduction frontend supplies the larger real-theorem chain.

The storage footprint is small; no large prime list, search result, certificate cache or numerical array was created beyond these essential sources and accepted proof artifacts. Existing science,549-module consumer, original main campaign and frozen helper bytes were not modified. Generic compiler/core-runtime/hardware assumptions remain the existing documented boundary; physical packed-data loader/caller/process association is not proved by this scout.
