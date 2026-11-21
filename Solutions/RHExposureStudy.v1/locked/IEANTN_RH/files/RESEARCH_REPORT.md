# IEANTN + RH research submission

The only global zero-placement hypothesis is the exact pinned Mathlib
RiemannHypothesis (SharedRH.lean). No GRH or proof of RH is claimed.
The prime functions are right-continuous; \(L=\log x\) and
\(\operatorname{li}=\mathrm{Li}_2+\operatorname{li}(2)\).
Results are unreviewed. Per-family derivations give exact statements,
definitions, sources, domains, and proof status.

| Family | Main results |
|---|---|
| PNT | For \(x\ge e^{34}\), CH2 with variable \(T=20\sqrt x/L\) gives \(|\psi-x|\le A(L)\sqrt x\), with explicit \(A\) in PNT.md. It improves both Lee–Nosal \(\psi\) formulas there. Signed prime-square and integrated transfers give theta and pi bands. A checked alternate \(A+.821\) route removes the numerical inverse-ordinate sum and consumes four more existing proofs; it retains RH and eight named source predicates. A two-range RvM written refinement reduces the cost to +.332. Laurent.md derives the coefficient-sign input mathematically with no coefficient sampling. |
| Intervals | Signed finite counts up to \(10^{19}\), including more than \(\sqrt x/\log x\) primes in \((x,x+2.91\sqrt x]\) on its admitted range from \(x\ge10^8\). For \(1\le\alpha\le2\), direct RH estimates use DGM and CMS. In particular \(x\ge4\cdot10^{18}\) and \(h=\tfrac{22}{25}(1+2\alpha)\sqrt x\log x\) give more than \(\alpha\sqrt x\) primes in \((x,x+h]\). This retains CMS's interior-prime term but does not beat their asymptotic Theorem 3. |
| Weighted | Exact endpoint-plus-tail formulas improve the factor 3 in the Lee–Nosal Mertens corollary on \(x\ge e^{34}\). After subtracting \((\psi-x)/(xL)\), the Mertens log-product error lies in \([.886,1.173]/(\sqrt x L)\). Normalizing instead by \(\log\theta(x)\) cancels the oscillatory endpoint and yields a primorial log-ratio margin \(1.876/(\sqrt x L)\), with no numerical ordinate sum. The downstream cancellation is also checked in Lean with the spectral band an explicit premise. |
| Ramanujan | Distinct routes give \(R_G\ge.001\) for all real \(x\ge6.1\cdot10^{11}\) and \(R_G\ge.04\) for \(x\ge6.4\cdot10^{11}\), respectively 11 and 8 certified analytic slabs joined to a monotone tail. The Table 2 slabs are unconditional with Büthe's published computation; the non-grid Johnston transfer gives margins on \([e^{42},e^{103}]\) using his finite-height prerequisites. The exact local real crossing is kernel-bracketed in \((38358837682.217926,38358837682.217927)\). Importing Johnston's early all-real coverage identifies this root as the largest real failure under RH. Full source-first verification of the early prefix remains open. |

## Actual reuse, and what changes

* RHAdapters/LogicalAdapters supplies finite heights and half planes.
  Strict density vanishes by emptiness, not a junk tsum equality.
  NetworkReuse.lean supplies full RH in place of the separate FKS
  density table, QRH, and finite-height RH premises of the existing
  \(\pi\) expansion and Ramanujan proofs. The old 25-input analytic gap
  theorem retains RH and 22 other named inputs, same onset/margin.
* BKLNW, CH2, QRH and FKS2 have distinct parameter domains. The legal
  fixed-strip beta=1/2 fallback is weaker than Schoenfeld. The useful
  route varies the height through CH2's actual finite-height interface.
  The low scaled spectral coefficient is additive: the verified relaxed
  numerical cap 11.1404 from existing analytic zero-count contracts
  transports .821 into the sqrt(x) coefficient, eliminating dependence
  on Platt's reciprocal sum. The actual CH2 Prop. 2.4, gamma-strip,
  and zeta-functional-equation proofs are consumed. No Challenge
  placeholder is used. TableCompare.lean gives normalized pi error
  \(<10^{-68}\) beyond exp(330) with the explicit li normalization,
  versus the old QRH \(5\cdot10^{-16}\) and historical \(1.6855\cdot10^{-12}\)
  allowances; not a claim of an upgraded Table 4 executable.
* Büthe Tables 1 and 2: local signed errors improve both finite interval
  counts and the finite analytic Ramanujan transition. The integrated
  J bridge recovers Table 1 information rather than assuming
  Table 2 globally. Row overlap handled by closed-cover tests.
  Mathlib Costa Pereira and PrimeInterval.v1 actual proofs are reused;
  MomentPNT and QRH power estimates are baselines, not inputs to the
  new sqrt(x)-scale conclusions. No Goldbach or GRH deduction is made.
* Existing source-linked count and exponential executions enter the
  exact **real-unit** gap formula and crossing proofs. New actual
  rh_coeff.c has a structured restricted-C AST corresponding to its
  bytes, with kernel-checked execution for 21 supported inputs. The
  outputs are consumed by the degree-20 polynomial and actual
  Ramanujan envelope, conditional on the analytic truncation and
  signed count estimates. The return-operator mutation is rejected.
  This is function-level source-first PV, not C compiler verification
  or verification of the rational slab program. Native stdout is a
  diagnostic; the finer 20-decimal crossing and real-slab scalars
  are exact rational execution evidence, not source-first PV.
* The old 1,755,663 scalar rows are not prime counts. FiniteClip.lean
  weakens their remaining count contract to **directed** bounds only,
  only where the row starts before the cut. At most 1,216,512 old rows
  and 2,433,024 bound sites at 610 billion versus up to 3,284,992 sites
  at the old 1.25-trillion cut. The census is not count truth, completed
  coverage, or a speed measurement.

## Reproduce and scope

Run /usr/bin/python3.10 -B reproduce.py /work/fresh_replay. The output
directory must not exist. This replays the new proofs against authorized
pinned application and generic objects, not a cold build of the inherited
application. It regenerates the three modified CH2 modules and compares
their bytes with the supplied sources. New successful axiom summaries
list only propext, Classical.choice, Quot.sound. See InputsNotClosed.md.
Published theorem and table inputs stay named; ordinary analytic proofs,
formal composition, source-first PV, and native/rational evidence are
separate. The supplied SOURCE_REQUESTS.json producer emitted a format
the broker rejected; the accepted legacy records are included alongside
it. Failed fetches were not treated as mathematical results.
