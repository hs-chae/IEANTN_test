# Refined reciprocal-density majorant (B0)

Use the validated D01 floor: its original P0, F and weight file are in d01_candidate.md §1 and d01_weights.txt; d01_cert.py and the offline replay check the numeric mesh from FKS. The new stage improves the integral in the mesh and activates the sharp power envelope earlier.

For s in [.70,.875], W(s)=2∑_{γ>H,β≥s}1/γ, H=3·10^12. FKS Cor.2.9 (PDF p.7) with Table 8 first block (p.26, a1=.77,H=3·10^12,k=1) gives N(s,T)≤c T^((8/3)(1−s))(log T)^(5−2s)+d(log T)^2 with c,d rounded upward in d01_cert.bracket. Integrating against 2/T² on [H,∞) upper-bounds W(s): each selected zero contributes 2∫_γ^∞ T^−2 dT; dropping the restriction to selected zeros in the count only enlarges the positive integral. Point choices at T=γ do not affect it. Put z=log H, r=(8s−5)/3, q=5−2s∈(3,4). The first integrated term contains e^(−rz) z^q ∫_0^∞ (1+t/z)^q e^(−rt)dt. Its fourth Taylor polynomial in t/z is an upper bound (negative fifth derivative on the positive axis). Thus
```
W(s) ≤ 2[c e^(−rz) z^q ∑_{j=0}^4 (q)_j/(z^j r^(j+1)) + (d/H)(z²+2z+2)],
```
with falling factorial (q)_j. This replaces the log-tangent integral of D01. Include new mesh points .87491 through .87499. Evaluate using directed log/exp and round weights upward, then take running minima since W is nonincreasing. The last upper weight is <.010454.

Use the D01 staircase argument: for successive mesh points s_j ending before .875 and with weights w_j, set F*(v)=
```
[(v/3+1)^2/6+2]e^(−.175v)+2.091v e^(−5v/24)
 + w_last + ∑_j(w_j−w_(j+1)) exp((s_(j+1)−.875)v).
```
The first term covers β<.70 up to T* with T=exp(v/3) in FKS Thm.3.2; the second is its explicit-formula error. Finite RH through H eliminates the β≥.70 group below H; QRH Thm.1.1 supplies the upper strip .875 inclusive. The same truncation-height conditions as D01 hold on v≥40; the bound on |ψ(e^v)e^−v−1| is F*(v)e^−v/8 there. Define C*(v)=F*(v)+1.000000147e^(−3v/8)+1.78e^(−13v/24) for θ by Dusart Cor.4.5 (PDF p.13). Both coefficients decrease on v≥40: positive weight differences, and the log derivatives of the polynomial prefactors are smaller than the negative exponent rates. Thus coefficients can be frozen at a left endpoint for a subsequent whole ray. The scripts use the new C* from v=185; quarter-floor freezing in finite cells is only for efficiency. Take the minimum with valid older coefficient bounds.

This reduces late-CH2-plateau losses in the Ramanujan join, and lowers the large-L endpoint loss in all signed Mertens branches. Neither a smaller upper coefficient nor the positive limiting mesh weight is evidence for a zero on the strip boundary or for an optimal exponent. Original density, truncation and RH computations retain their source trust.
