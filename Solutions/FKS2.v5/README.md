# QRH through the FKS2 correction application

This is the conservative application extension requested for qrh-2pv. The original
`FKS2Numerics.v1.nuAsympE30` and C program remain fixed. The donor's corrected
calibration proves 6.339e-7; the old 6.3376e-7 premise is refuted and excluded from
all new positive proof closures.

The baseline was established in local commit 7bb689207f2cd949786a12afb9cf46602d143e5d:
A=121.096, L=300, coefficient anchor30, unchanged41/42term loops. Its numerical
provider is FKS2Numerics.v3.baseline_bound, and its FKS2.v4 consumer proves a prime
in (x,x+x/16] for x>=exp300. The update changes only the configured A literal to
0.0000000001. FKS2Numerics.v4.updated_bound certifies the corresponding correction
through an explicit reciprocal-A target/output transport of the original
source-derived summation-stability proof. These are configured sources, not one
unchanged binary or an unrestricted parameter evaluator.

FKS2QRHAdapter proves the whole-ray same-shape psi input from the actual existing
1/566 QRH-CH2 estimate. The same FKS2 Proposition13 and PrimeInterval criterion
then prove width x/10000000000000. The final coefficient A*(1+nu_upper) strictly
decreases; the correction nu itself increases when A decreases. The existing
direct QRH route already proves the stronger width x/60000000000000 on this
range. This experiment establishes application-level propagation, not a
best-known result or automatic theorem discovery.

Build in this directory with `lake update` and `lake build Solution FKS2NodeReplay`.
The canonical compiler is Lean4.34.0-rc2. FKS2NodeReplay takes13named analytic
premises, BKLNW Corollary5.1 and QRH; baseline additionally takes FKS.v2's classical
psi bound. A separate private Lean4.34.1 source replay supplies the published
OpenAI QRH proof. No incompatible compiled objects are imported.

The numerical proofs use disclosed finite native_decide facts, restricted-C
constructor semantics and the approved binary64/compiler/runtime boundary.
They are not three-standard-axiom Comparator receipts. Conditional pipeline
solutions accept exact typed numerical premises, and the assembled replay
supplies their actual providers. No Challenge is imported by a solution.

Donor: hs-chae/goldbach_pv, hs-chae/fp,
3b3205d18546726c51e3b832699a675e84a82aba. Network parent:
d85631a387a9b374a43ef1732b0b3ca5506eab6a. OpenAI proof:
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The donor FKS2.v3 namespace was not
copied because this network already used that version for Phase2 hybrids.
