# Recorded development corrections

All failed development attempts remain outside accepted source/receipts. Original trial files and historical primary outcomes were never modified.

- Initial exponential decimal lower bounds were insufficient for the chosen tight scalar constants. Replaced them with kernel-proved exp(4)>54.59813 and exp(4.005)>54.8718; the finite Taylor obligations passed.
- Several early Lean elaboration/algebra failures involved explicit rational coercions, additive/multiplicative association, casts and inequalities whose nonnegative summands were not supplied. Corrected the proof terms; no assumptions were added.
- A broad edit restoring a ring normalization matched a prefix of another local name. Restored the intended exact identity and recompiled the immutable snapshots. Failed attempts are not accepted evidence.
- One development dependent compile was launched before reading the provider result; its missing-module failure was preserved. Final replay orders every import dependency sequentially from source.
- During development a source was edited while a copied snapshot compiled. Development receipts identify the executed snapshot. Final source-only runs freeze every source and reread all original hashes before acceptance.
- The initial new-lane reproduction draft had lib.parents[4] in its generic package guard, incorrectly selecting the packages directory. Actual CLI execution rejected before creating a run. Changed this NEW lane to parents[3] and verified real CLI guards in normal/-O/-OO modes. The existing accepted parent runner already used parents[3] and was not modified.
- One tool output was truncated at context exhaustion. No completion was inferred from it: filesystem and live-process checks confirmed that no final run had started; the actual final run was launched and checked explicitly.
