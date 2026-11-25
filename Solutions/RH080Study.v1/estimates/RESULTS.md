# Source-enriched cube counts and actual zero-count envelopes

This is kernel-only Lean verification (D), with named literature input predicates (B), **not** source-first program verification (C). No result below is claimed to be a global literature record. The three original analytic inputs for the cube result are ordinary RH, the general refined theta estimate of Schoenfeld1976 Theorem10(6.1), and the two existing canonical finite theta clauses of Büthe2017v2 Theorem2(1.6),(1.7). Source enrichment changes the assumption package relative to the old Octic family; no automatic dominance between those packages is claimed.

## Strongest actual new cube theorem

`ThetaCubePopulation.v1.challenge_cube_density_0965` proves, for **every real n>=exp6**, that the number of prime p with n³<p<(n+1)³ is strictly greater than `(193/200)*n²/log n = 0.965*n²/log n`. Both endpoints are strictly open. The natural-number consumer starts at n=404. The finite theorem on exp6<=n<=2,000,000 consumes only the two Büthe predicates and has **no RH premise**.

The previous source-conditional adaptive-Octic result was >0.7*n²/log n for all real n>=exp8. The new result improves the coefficient and real onset, with a different explicit source package. This is a useful network/source demonstration, not a causal exposure result and not a claim that classical prime-between-cubes mathematics was unknown.

The proof does not sample n. It splits at n=exp(29/2), which is strictly below2,000,000. Below that split, both cube endpoints are inside the actual Büthe range [1423,10^19]. The positive sign `x-theta(x)>0.05*sqrt x` is consumed to obtain theta(n³)<n³; it is not discarded into two absolute-error allowances. The upper endpoint has theta((n+1)³)>= (n+1)³−1.95*sqrt((n+1)³). A finset argument proves that removing a possible upper-endpoint prime costs at most log((n+1)³), equivalently one count.

Above the split, the two actual Schoenfeld theta errors retain the `(log x−2)*log x` term. Polynomial lower bounds for exp on the entire real ray prove `(log n)²−0.66*log n < (10034/70000)*sqrt n`. This closes the whole infinite region with a strictly positive rational margin. The weaker0.96 coefficient at the old exp8 onset is also fully proved and preserved as an intermediate result.

## Exact zero-count source envelope

`BellottiWongZeroCount.v1` records **both** actual bounds in Bellotti–Wong2025 Theorem1.1 (arXiv2412.15470v2,07Jul2025; DOI10.1090/mcom/4133), valid unconditionally for T>=e, with 0<gamma<=T counted with multiplicity. The source main term M0 has **no7/8**. The canonical BPT bound uses Q=N−(M0+7/8). A proved triangle inequality therefore adds7/8 before comparing the sources.

With L=log T, the common-center allowances are:

- BPT: `0.28 L`.
- BWfirst: `0.10076 L+0.24460 log L+8.95844`.
- BWsecond: `0.11200 L+0.12567 log L+4.64917`.

`ZeroCountEnvelope.v1.challenge_off_ordinate_envelope` proves the actual zero-count bound by the minimum of all three, consuming canonical BPTOffOrdinate.v1.bound and both BW source clauses. The proof preserves BPT's non-zero-ordinate hypothesis and T>2pi; it does not silently claim a new proof at jump points. The same Solution proves the identity between the expanded source main term and the paper's literal `T/(2pi)*log(T/(2pi*exp1))` on T>0.

Three separate whole-real activity theorems prove that BPT is strictly better than both BW allowances on1<=L<=25; BWsecond is strictly better than BPT for everyL>=32; BWfirst is strictly better than BPT for everyL>=60. These are sufficient activity regimes, not exact optimal crossover points. This new node is a reusable **secondary estimate**: no new prime-gap coefficient or ANT numerical gain is claimed until an actual ANT consumer uses it. Ranking only the leading0.10076 coefficient would miss the useful second BW inequality.

## Source identity and inventory limits

The actual24-page Schoenfeld original was recovered from the preserved primary corpus and p337 was independently inspected as an image. Its primary SHA is `8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897`. The initial publisher response was a different57-page AMS website PDF and is quarantined as non-source evidence. The frozen ablation source-fact file is unchanged; later recovery is recorded separately in PRIMARY_SOURCE_RECOVERY.json.

The actual17-page Büthe v2 PDF SHA is `350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1`. Exact(1.6),(1.7) were read directly. These clauses already existed in Buthe.v1; claiming them absent would have been wrong. The newly introduced source node is Schoenfeld's refined6.1, not Büthe's numerical theorem. Current Lee–Nosal v4 (2Oct2025) also contains a theta theorem; older v3 only-psi descriptions are not a current source census.

RH_ESTIMATE_CATALOG.csv/JSON is a **declared17-row subset inventory**, not an exhaustive audit of every IEANTN source claim. Physical identity is(file,declaration,LFline), with exact current statement and sourceSHA. Six source claims are consumed by the selected new proof paths, six other typed nodes are not used by these new paths, and five exact canonical claims were not found in the selected census. “Not consumed here” never means globally unused. Exact source-normalization/reconciliation and original-locator tasks remain explicitly pending on the affected rows; the inventory does not falsely mark them completed source reviews.

In particular, the current BW primary text reports both its useful second bound and a correction to an older HSW constant. That is a provenance task requiring the original HSW center and statement, not permission to introduce an unreconciled bound. Neither issue affects the new cube proof.
