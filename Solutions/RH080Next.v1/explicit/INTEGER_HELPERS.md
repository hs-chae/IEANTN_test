# Verified source integer helpers

The preserved `pv/fft/w4_fft.c` and `pv/fft/fap_fft.c` now have complete source-to-AST, execution and correctness contracts for `magnitude_compare`, `increment_words`, and `divide_small`. Their final ANT connection is pending. Under the owner's definition, these standalone helper contracts do not yet constitute completed source-first PV. The complete FFT program and its numerical norm output are not claimed source-verified here.

For base B=10⁹, `increment_words` proves Pout + carry·Bⁿ = Pin+1, normalized output digits and carry≤1. `divide_small` proves the exact floor quotient when ceiling=0 and the exact ceiling quotient when ceiling=1, with return status zero. The supported division domain is 0≤n≤6, 1≤d<B and normalized input digits. It includes n=0, zero data, exact divisibility, positive remainders and the actual N=131072/N=16777216 divisors.

The proofs execute the genuine source AST: pointer/flag parameter binding, every source loop iteration, all temporary declarations and scope exits, unsigned word arithmetic without overflow or underflow, the optional nested `increment_words` call, and caller restoration. Every permitted call execution has the same return and final state as the proved terminating execution. The `PureArgs.args_sound` theorem handles every permitted argument evaluation order. Target-slice output, all other words in that allocation, and other caller objects are explicitly related to the original data.

Each original C file is paired with its independently proved syntactic correspondence. The reproduction script additionally checks that the exact C bytes equal the formal source string, compiles those preserved files, and compares 160 deterministic increment/division cases per file against independent Python integer arithmetic. These execution tests supplement the general Lean proof.

Reproduce from the campaign's pinned Lean/mathlib dependency environment:

```sh
python Solutions/RH080Next.v1/explicit/reproduce_fft_integer_helpers.py \
  --context /path/to/clean_proof_context.json --out /fresh/experiment-directory
```

The context contains the exact compiler hash, package commits and eight generic library paths. The driver copies the source, emits exact source/build/run hashes and receipts, performs the native tests, and rebuilds the complete 71-source proof closure without application-object fallback. Use `python -O` or `python -OO` for the corresponding controller checks. Acceptance uses explicit checks rather than Python assertions.

All three actual CLI modes passed: 984.50, 987.60 and 985.81 seconds; each peak Lean RSS was approximately 37.01 GiB, with zero OOM events. Exact receipts and the 19-source publication inventory are in `INTEGER_HELPERS_MANIFEST.json`. All audited theorem closures contain only `propext`, `Classical.choice` and `Quot.sound`.

The immutable historical run receipts retain their original `source_first_helper_PV_complete` field. That field recorded only the helper-contract milestone; it does not establish an actual IEANTN theorem connection. The exact executed controller is preserved alongside each receipt. The current manifest and future controller results explicitly mark source-first PV incomplete and the final ANT connection pending. This terminology correction changes no numerical source, Lean proof, acceptance gate or historical outcome.

The trust boundary remains the adequacy of the specified restricted C execution model and the selected LP64/ULL64 ABI, plus the pinned compiler/core runtime, OS and hardware. Source checking and application correctness are proved; a complete ISO C semantics proof or whole-FFT compiled execution correspondence is not claimed. Application input arrays and digit bounds are explicit preconditions that the enclosing program must establish.

`ExplicitFFTAdd*` and `ExplicitFFTSub*` are subsequent work on the actual `fixed_add` helper. Their digit-loop development does not yet constitute a completed full-call contract and is excluded from this integer-helper acceptance inventory.
