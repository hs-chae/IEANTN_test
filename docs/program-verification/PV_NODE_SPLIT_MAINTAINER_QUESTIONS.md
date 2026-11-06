# Program verification and nodes: decisions for the maintainers

Each question names a recommended default, what it costs, and what it changes. Nothing here has been
implemented; the only code written for this study is a hypothetical node in a disposable local worktree
(`agentB/pv-node-split-exp`, never pushed). References: upstream `teorth/IEANTN@466b41b`, PoC
`hs-chae/IEANTN_test@qrh-2pv_B 3280a3c`.

## Q1. Is a new proof of an existing statement a new node?

**Recommended: no.** A new program, a new partition, a kernel-only route or a reduction of native facts
for an unchanged statement is new *evidence*: a justification (designated or spare) of the existing
conclusion, or an entry in the local evidence registry. A new node or version is right only when the
statement or its imports change (`new-version`, ARCHITECTURE §5).

*Why it needs deciding.* The PoC already broke it once: `FKS2Numerics.v7.qrh_pi` repeats
`FKS2Numerics.v5.numerical_pi` (same fingerprint, same imports) and the copy spread to the consumers
`FKS2.v7`/`FKS2.v9` (3 duplicate statements). *Ramification.* None for existing nodes (versions are
variants and stay); it governs new work.

*Guard.* A new route may be **designated** only if its unproved leaves are contained in the current
designated route's; otherwise it stays a spare. Upstream enforces this for bridges (`67b277c`); the PoC
branch predates the check, and upstream's checker run on the PoC graph rejects 4 re-designations from
`6af2f7a` that made the unconditional zero-free region (`RosserSchoenfeld.v1`) and two `FKS.v2` bounds
rest on QRH.

## Q2. Where may the Lean proof behind a justification live?

`check-graph` requires `Solutions/<NodeId>/Solution.lean` for `lean-noncompliant` (`ieantn.py` L1568–1585),
and receipts name the node's own solution project. So a second proof route that lives in another
solution project (as `Solutions/Table4Evolution.v1` does for `FKS2Numerics.v6/v7`) has no place in the
justification list, and new node versions are the path of least resistance.

**Recommended default: no schema change now.** Use the pattern measured in the experiment: a thin
`Solutions/<NodeId>/Solution.lean` that requires the route's project by path and applies its theorem
(report §7: 5 files, a one-line proof; the build stayed fresh through the cross-project import). One
caution: in that workspace 13 path dependencies also root a module named `Solution`, so `import Solution`
resolving to the right module is not guaranteed by anything (cf. `cb2983e`). *Alternative for later:* an optional field on
a justification naming its solution project and theorem. That touches `check-graph`, `verify`,
`record-receipt` and the Palomar-shaped metadata, so it is an upstream decision.

## Q3. Should source changes in another solution project be visible to `status`?

`solution_drift` (`ieantn.py` L2355–2385) diffs only the receipt's own `Solutions/<project>`. A proof
that reads a C file from another solution project by `include_str` is therefore blind to a change in that
file (measured in the experiment, report §7). Also, `drift_note` files a changed `.c` file under "no Lean
source among them", the phrase meant for the benign case; for program-verified evidence the C file is the
proof object.

**Recommended:** extend the drift check to the solution manifest's path dependencies, or record the hashes
of every file a solution reads at verification time. Small tooling change, upstream decision. Until then,
the local gate's SHA-256 pins on declared sources cover the gap for Agent B's endpoints.

## Q4. What do node pages show for program evidence?

**Recommended:** the designated kind as now; under it, separately and labelled *local, non-official*, the
local attestations (method `lean-verified-program`, native-fact count, source hashes). Never colour a
local attestation like a receipt, and never write `lean-comparator` without a receipt (NODES.md L211–221).
The PoC's page generator already shows proving theorems and a "complete local proof" row.

## Q5. Adopt the promotion rule as guidance?

Promote a numerical result to its own node only if at least one holds (report §6):
R1 two or more consumer *families* need the same statement; R2 its evidence is weaker than its consumer's
Lean step, so keeping it inside would push the consumer below Comparator eligibility; R3 it is an
externally meaningful statement of record (finite RH, zero counts, a published table's bound); R4 the
combined solution would exceed the one-hour verification budget (ARCHITECTURE L331–335) or a
runner's memory.

**Recommended:** documentation and housekeeping guidance, not a CI rule. Tested against the PoC's 27
computation nodes, R2 or R3 explains 25, R1 only 1 (by family), and the 2 others are a formalized
statement of record with no consumer yet and an asserted computation.

## Q6. What to do with the existing duplicate `FKS2Numerics.v7`?

**Recommended: leave it.** It is frozen, `FKS2.v9` imports it, and deleting it would need migration.
Optional later: two trivial bridges (the statements are identical) and `deprecate FKS2Numerics.v7 --for
FKS2Numerics.v5`, with v7's proof recorded as a spare justification of v5.

## Q7. Register Agent A's winner as a provider node?

**Recommended: not now.** Its statement is Vocabulary-expressible (`HasPowerLogBound Eπ 0.00947147 0
(7/8) (exp 300)`), but four of its seven hypotheses are solution-level (`OriginalCHJSource`,
`PrimaryInputs`, a solution height constant) and there is one consumer family. A node would first need
the source facts stated in a `Conclusions.lean` with node-local definitions (mollifier, source moments,
rectangle bound), not in Vocabulary until a second node needs them. Revisit if those source facts gain an
independent consumer.

## Q8. Try a real Comparator run on a kernel-only numerical provider?

Twelve program results now need no native evaluation (the PoC's kernel routes). A kernel-only provider
behind a thin node solution is, in shape, `lean-comparator`-eligible. It would be the first receipt for
a program-verified numerical bound. The obstacle is resources, not policy: the kernel routes peak at
14–37 GB and 45–264 s per module, and `verify-comparator.sh` runs a plain `lake build` on a CI runner.

**Recommended:** owner's call; if wanted, start with the smallest (`power_network.c`, 49 s, 14 GB) on a
branch, through `ieantn.py verify`. No receipt can be produced locally.

## Q9. `imports_status` for a provider that reads a program

**Recommended: `identified`** when every mathematical input is an edge. The program and its data are
evidence for the step, not inputs to it, so they do not make the status `traced`. Use `traced` only for
real non-edge inputs (an external algorithm or data set the claim rests on, NODES.md L186).

## Q10. A source-linked proof and an older `numerical` citation for the same conclusion

**Recommended:** designate the in-repository proof (`lean-noncompliant`, with its native facts named in the
note) when the local gate passed, and keep the citation as a spare. Precedent:
`FKS2Numerics.v2.nu_asymp_e30_le` designates its source-linked proof; that verification also found the
cited threshold wrong (`6.3376e-7`, replaced by `6.339e-7`), which is why it is a new statement rather
than a second justification. The status view keeps reporting such a proof as unverified, which is
accurate.
