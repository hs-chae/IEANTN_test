# Strict prime counts between consecutive real cubes

**Two-source theorem (B, written proof).** Assume ordinary RH and the named Schoenfeld (6.1) and Büthe (1.6)–(1.7) inputs below. For every real \(n\ge e^8\),
\[
 P(n):=\#\{p\ {\rm prime}:n^3<p<(n+1)^3\}
   >0.9669924\,n^2/\log n.
\]
The finite subrange \((n+1)^3\le 10^{19}\) alone has coefficient \(0.98868\), without RH from the Büthe inputs. A one-source comparison gives \(0.7436\) on the full ray from RH and Schoenfeld (6.1) alone. The exact pointwise bounds below are preferable to splicing constant coefficients. See smooth.md for a separate strengthened source combination if present. No new Mathlib RH-only theorem, source-first program verification, or optimality is claimed.

## Named premises with primary locators

Write \(\theta(x)=\sum_{p\le x}\log p\) (actual primes, natural logarithm, inclusion at \(x\)). Set \(T=10^{19}\) and \(S(x)=\sqrt x(\log x-2)\log x/(8\pi)\).

* **(S):** Ordinary RH implies \(|\theta(x)-x|<S(x)\) for all real \(x\ge2300000000\). Lowell Schoenfeld, *Sharper Bounds for the Chebyshev Functions θ(x) and ψ(x). II*, Math. Comp. 30(134) (1976), 337–360, Theorem 10, (6.1), printed p. 337 / local PDF p. 1, DOI 10.1090/S0025-5718-1976-0457374-X. /corpus/literature/Schoenfeld1976.pdf is the **recovered primary**: 1,795,864 bytes; SHA256 8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897, agreeing with the primary-pin addendum. The wrong publisher-response digest in the preregistered packet is not used.
* **(B1):** \(\theta(x)\ge x-1.95\sqrt x\) for \(1423\le x\le T\).
  **(B2):** \(\theta(x)<x-0.05\sqrt x\) for \(1\le x\le T\).
  Jan Büthe, *An analytic method for bounding ψ(x)*, arXiv:1511.02032v2 / Math. Comp. 87 (2018), 1991–2009, Theorem 2, (1.6)–(1.7), preprint printed p. 2 / PDF p. 2, DOI 10.1090/mcom/3264. /corpus/literature/Buthe1511.02032v2.pdf: SHA256 350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1. These finite inequalities are published computational results without a global RH hypothesis. We neither recreate nor verify the source program. Only the stated theta inequalities are imported from these two papers.

## Strict endpoints and pointwise bounds

Write \(a=n^3,\ b=(n+1)^3,\ P=P(n)\), and \(\theta(b-)=\sum_{p<b}\log p\). Then \(W=\theta(b-)-\theta(a)\) is exactly the log-weighted strict-open count. Subtracting \(\theta(a)\) excludes a possible prime at \(a\). On some left neighborhood of \(b\) the prime sum is constant with value \(\theta(b-)\); a continuous lower bound valid there persists at \(\theta(b-)\), with weak inequality. In particular (B1) works at \(b=T\); (S) works here since \(b\) is above its lower cutoff. No subtraction of 1 or \(\log b\) is needed. A strict upper bound for \(\theta(a)\) makes the inequality for the difference strict. Also \(W\le P\log b\).

Use \(U(a)=S(a)\) if \(a>T\), and \(U(a)=-0.05\sqrt a\) otherwise. Use \(D(b)=S(b)\) if \(b>T\), and \(D(b)=1.95\sqrt b\) otherwise. These are the better available respective one-sided error bounds (on the ray \(S(x)>1.95\sqrt x\), since \(\log x\ge24,\ \pi<4\)). We have
\[
 P>\frac{b-a-D(b)-U(a)}{\log b}. \tag{1}
\]
In the seam \(a<T<b\) one can also discard the at-and-above-\(T\) portion to get \(P>(T-a-1.95\sqrt T+0.05\sqrt a)/\log T\); take the max. At \(a=T\), use (1) only. Do not use Büthe at \(b>T\) by replacing \(b\) with \(T\) in the error while retaining \(b-a\) as the main term.

Another direct improvement uses exact summation by parts:
\[
 P=\frac{W}{\log b}+\int_a^b\frac{\theta(t)-\theta(a)}{t\log^2t}\,dt .
\]
Integrate \(\log p/(t\log^2t)\) from \(p\) to \(b\) for each \(a<p<b\) to see the identity (the value at \(t=b\) is immaterial). A certified correction to (1) is the integral with numerator \(\max(0,t-a-D(t)-U(a))\). Without (B1),(B2), use \(S\) for both errors throughout.

## Uniform envelopes and slack

Let \(m=2980<e^8\), so both lower source cutoffs hold at the cube endpoints. Let \(L=\log n,\ x=1/n,\ y=\log(1+x)\), with \(0<y\le x\). Normalize all counts by multiplying by \(L/n^2>0\). The main term in (1) is
\[
 G(n)=\frac{1+x+x^2/3}{1+y/L}\ge1+\frac{7}{8(n+1)}>1.
\]
Indeed \(x+x^2/3-y/L\ge7x/8\) and \(1+y/L\le1+x\). For \(0\le x\le1\), \((1+x)^{3/2}\le1+2x\) by squaring.

If \(b\le T\), the normalized error is at most \((1.9+3.9/n)/(3\sqrt n)\): first bound \(1.95(1+x)^{3/2}-0.05\), then use \(L/(L+y)\le1\). Thus the normalized count is strictly greater than \(1-F(n)\), where
\[
 F(n)=\frac{1.9+3.9/n}{3\sqrt n}-\frac7{8(n+1)} .
\]
\(F'(n)\le-1.9/(6n^{3/2})+7/(8n^2)<0\) for \(n\ge2980\). Hence \(F(n)\le F(2980)<0.01132\).

The normalized two-sided Schoenfeld error is at most
\[
 \frac{(2+2/n)(3L+3/n-2)L}{8\pi\sqrt n}.
\]
Cancel \(\log b\) in \(S(b)\), bound \(\log a/\log b\le1\) in the term for \(S(a)\), and use the bounds on \(y,(1+x)^{3/2}\). For \(n\ge M\ge2980\) it is at most
\[
 H(M)=\frac{(1+1/M)(3\log M+3/M-2)\log M}{4\pi\sqrt M}.
\]
Indeed fix \(1/M\) in place of \(1/n\) and differentiate \(u(3u+c)e^{-u/2}\) at \(u=\log n\ge\log2980>7\), with \(c=3/M-2\in[-2,0]\). The sign is that of \(-3u^2/2+(6-c/2)u+c\le-3u^2/2+7u<0\).

Since \(2154434^3<T<2154435^3\), \(b>T\) implies \(n>2154433\), and both errors can be bounded by Schoenfeld (this weakens the available left-endpoint Büthe inequality in the seam). For \(2154433<n\le2160000\), use \(H(2154433)<0.033007995\) and \(G(n)\ge1+7/(8(2160000+1))\). For \(n\ge2160000\), \(H(2160000)<0.033\) suffices. These enclosures and the Büthe case certify a common slack \(>10^{-8}n^2/L\) above \(0.9669924n^2/L\). With Schoenfeld alone, split at 3000: below this use \(H(2980)<0.256640\) and \(G(n)\ge1+7/(8(3000+1))\); starting at 3000 use \(H(3000)<0.2564\). See certify.py for the exact rational checks; the calculus gives coverage of complete real intervals.

## Onsets, comparisons and limitations

Under (S) and RH, on any ray \(n\ge M\ge e^8\) the coefficient \(1-H(M)\) is admissible. For example the rational checks give \(0.9707,\ 0.98119,\ 0.99219,\ 0.99686\) at \(M=3\cdot10^6,10^7,10^8,10^9\), respectively. From (B1),(B2) alone one has \(1-F(M)\) on any band \(e^8\le M\le n\le T^{1/3}-1\). These are sufficient onsets, not minimal ones. Schoenfeld plus the reverse endpoint comparison (upper at \(b-\), lower at \(a\), and \(W\ge P\log a\)) also gives \(P\log n/n^2\to1\): the main terms tend to 1 and the errors are \(O((\log n)^2/\sqrt n)\). No constant strictly greater than 1 works on any full ray. This does not exclude coefficient 1.

For disjoint contained octic windows with permitted parameters, adding the stated inherited family’s lower expressions cannot compete: \(-0.91015+4.2/\log u<0\) and the leading term is \((8/9)(\text{width})/\log u\). Since \(\log u\ge3L\), the normalized sum is at most \((8/9)(1+1/n+1/(3n^2))<0.8892\). This is not an upper bound on actual prime counts, and does not prohibit other uses of the explicit formula. The inherited octic result uses RH + Green + Nicolas + BPT, a different B package.

At the integer \(n=2154435\), both endpoints exceed \(T\) and the exact normalized RHS of (1) is below \(0.967\) (exact enclosure in certify.py). The plain two-endpoint lower bound has a bottleneck near the end of Büthe’s finite domain, not at \(e^8\). This negative comparison is for that expression only, not an impossibility theorem about the premises. Extending Büthe past \(T\), using overlapping windows without deducting duplicate counts, or inferring a whole-real ray from sampled scans is unsupported.

The argument uses no CMS, no compact-dual C program, and no kernel norm premise. Tier B describes the disclosed analytic inputs; the scalar checks are rational written-proof checks, not claimed to be new kernel certificates. No assumption is hidden as an axiom and no literature-record claim is made.
