# Round 3: generic correctness theorems and their real consumers

Rule followed: a generic lemma is added only when at least two actual applications need it.
Line counts are code lines of the Lean files (comments included where noted).

## 1. `Table4Evolution.pi_bound`: the Table 4 transport for any partition and profile

| Generic part | File | Lines | Axioms |
|---|---|---|---|
| `whole_ray`, `tiles_le`, `cell_le`, `kernel_integral_le` (transport over any tiling of `[300, 330]`) | `Partition.lean` | 162 | standard |
| `cellsOK`/`cellsOK_sound`, `cellsOf_valid`, `constOK`/`constOK_sound`, `expUp` | `Bounds.lean` | 241 | standard |
| `pi_bound`, `program_bound`, `chunked_bound` | `Instance.lean` | 88 | standard |
| `profile_qrh`, `profile_step`, `profile_power` | `Profiles.lean` | 72 | standard |

**Consumers (5 configurations, 3 profiles, 2 program shapes):**

| Configuration | Profile | Program shape | Per-instance code (non-blank, non-comment) | Remaining obligations |
|---|---|---|---|---|
| `QRHTrunc` (2 cells) | QRH | `PVCore.Program` | 16 lines | 1 certificate (native) |
| `QRHTrunc.Kernel` | QRH | `PVCore.Program`, kernel route | 16 lines | 4 `decide +kernel` |
| `OldTrunc` (3 cells) | step | `PVCore.Program` | 16 lines | 1 certificate |
| `QRHQuarter` (120 cells) | QRH | `PVCore.ChunkedProgram` | 22 lines | 1 certificate |
| `AgentATrunc`, `AgentASource` (4 cells) | power | `PVCore.Program` | 15 lines each | 1 certificate |

Each instance proof is the same three lines: `pi_bound (profile_…) hAnchor certificate.… (by decide)
certificate.… (program_bound certificate.… …)`, then normalizing the bound's decimal.

**Against the round-1/2 code.** The QRH-specific 30-cell proof `FKS2Table4` (FKS2Numerics.v5) is
953 lines with a fixed partition; `FKS2Pair` generalized it over profiles but not partitions
(`GenericMath.lean`, 152 lines, plus about 260 per profile for its inputs and certificates). A new
partition or profile now costs only generated data and one certificate. The old files are unchanged
and still build: they are the fair baseline.

## 2. `PVCore.decode_of_decodeL`: literal decoding in the kernel, three programs

`Solutions/ProgramVerification/PVCore/Decimal.lean`, 199 lines, standard axioms. For every string
and program: `decimalL s = some q → decimal s = some q` and `decodeL p = some v → decode p = some v`.

| Consumer | Program | Kernel cost |
|---|---|---|
| `PVPilot.KernelOnly.decodeA` | calibration stage A (7 literals, `calibration_new.c`) | with B: 16 s, 7.9 GB (module) |
| `PVPilot.KernelOnly.decodeB` | Ramanujan budget stage B′ (7 literals, `ramanujan_9401_new.c`) | as above |
| `Table4Evolution.QRHTrunc.Kernel.decode_k` | 2-cell Table 4 transport | within the 147 s module |

## 3. `PVCore` bridges reused

| Lemma | Round-3 consumers |
|---|---|
| `PVCore.le_bound_of_check` (single `sum` call) | `QRHTrunc`, `OldTrunc`, `AgentATrunc`, `AgentASource` (via `program_bound`) |
| `PVCore.le_bound_of_checkChunked` | `QRHQuarter` (120 entries; the first chunked instance used for new mathematics) |
| `PVCore.upperCheck_of_decode` (round 2) | `QRHTrunc.Kernel`, `PVPilot.KernelOnly` |

## 4. `QRHGlobal`: the tertiary pieces

| Lemma | Consumers |
|---|---|
| `interval_of_theta_power` (power bound on `Eθ` → primes in `(x, x + c·x^{7/8}]`) | `global_interval` (row `(80, 0.23719)`, `c = 1`), `sixteenth_interval` (row `(128, 0.03013)`, `c = 1/16`) |
| `ladder_sound` (prime ladder for `c = num/den`) | `c = 1` (32 rungs from 2), `c = 1/16` (230 rungs from 1361) |
| `dusart_piece` | both, with different pieces |
| `kl_piece` (Kadiri–Lumley row → short intervals) | `sixteenth_interval`, two rows |

## 5. Compile and check costs (this machine, 128 cores, warm dependency caches)

| Target | Wall time | Peak memory |
|---|---|---|
| `Table4Evolution` configuration modules (native certificate) | 4–5 s each | — |
| `Table4Evolution.KernelOnly` (2 cells, kernel only) | 128–147 s | 27.8 GB |
| `PVReplay.KernelOnly` (A→B′ decoding in the kernel) | 16 s | 7.9 GB |
| `PVReplay.KernelChain` (round 2, the rest of the chain in the kernel) | 177 s | 22.7 GB |
| `QRHGlobalIntervals` (all modules, ladder by `decide`, 261 primality proofs by `norm_num`) | ≈ 8 s | — |
| Gate, one endpoint (`native_assisted_check.py check`) | 60–70 s | 8.9 GB |
