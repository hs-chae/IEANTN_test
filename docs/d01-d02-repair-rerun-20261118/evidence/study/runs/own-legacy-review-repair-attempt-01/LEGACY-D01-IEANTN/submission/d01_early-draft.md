# Study A-D01: draft
Baseline retained: PT Theorem 2 and Dusart Theorems 5.6, 5.7, 5.9, in their literal domains. Project's repaired Dudek–Platt criterion is not being treated as a numeric estimate.
Routes under development: CH2 finite-height estimates can bridge the Ramanujan intermediate region; QRH + FKS (explicit formula and density) can replace the hypothetical asymptotic input with an admitted original-theorem consequence. Direct partial summation using sums over prime powers avoids charging the full prime-power correction twice in Mertens bounds.

## Derivation planned for power-saving ψ
Use FKS Theorem 3.2 (PDF p.8, parameters (40,1/2,0,2.091)); not its Proposition 3.4. Choose T=x^(1/3). Split |gamma| into the low part controlled by reciprocal-zero sum and the high-beta part controlled by FKS Corollary 2.9 and Table 8 (PDF pp.7,26), using the a1=0.77 constants. For s>5/8, y=log(3*10^12), r=1-(8/3)(1-s), q=5-2s, the latter gives total weight (both signs) at most
2[c1 exp(-r y)y^q/(r-q/y)+c2 exp(-y)y^2/(1-2/y)]
provided r>q/y, because there are no zeros of beta>=s up to H, and d(log u)/du<=1/y for u>=y. Combine with original QRH Theorem 1.1 (PDF p.4); boundary beta=7/8 allowed. This method can give a pure-power envelope, not merely the original O(x^(7/8) log²x) shape.
