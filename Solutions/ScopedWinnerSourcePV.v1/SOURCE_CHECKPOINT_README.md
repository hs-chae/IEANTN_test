# Replayed source-only partial checkpoint

Extract `source-checkpoint-v2.tar.xz` into an empty directory. No binary or
application object is supplied. Use the official Lean4.34.0-rc2 toolchain and
Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6 with its eight pinned public
package libraries available. The exact commits and source hashes are checked by
`SOURCE_LOCK.json`.

```
python3 source-checkpoint-v2/reproduce_guarded_v2.py --toolchain /path/to/lean --mathlib /path/to/mathlib --out /fresh/output --receipt /fresh/guard-receipt.json --jobs 4
```

The actual fresh host replay compiled142 application/backend modules from
source with an empty application object directory, audited five source-binding
roots to standard axioms, and compiled/executed all52 C++ rows. It passed in
1760.70s; the C++ execution took1320.40s. Maximum individual process RSS was
10530025472bytes, and the48GiB resource scope recorded zero OOM events.

This proves syntax/source association and partial helper facts. The original
final theorem still has49 native dependencies. The 68-function application
proof and final isolated theorem-consumer migration are unfinished. The replay
is host source-cold evidence, not final namespace-isolated PV acceptance.

The V2guard separately checks the real kernel/runtime/sharedlibraries/stdlib
and168 platform headers, as well as the thin launcher. Its normal/-O/-OO
preflights and9 wrong-runtime controls passed. The full142/734/52 replay is
the preserved V1run; it is not relabelled as a new fullV2execution.
