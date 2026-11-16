// Copyright (c) 2026 IEANTN contributors. Apache-2.0.
// NEW raw numerical scout, NOT yet source-verified. No computed outputs embedded.
#define main archived_basis_main
#include "basis_fp128_height_v2.cpp"
#undef main
#ifndef HEIGHT_CELLS
#define HEIGHT_CELLS 4096
#endif

static I expPositiveRaw(I x) { return divI(unit(),expNeg(x)); }
// Same real functions. Endpoint calls use exp/log monotonicity to avoid
// repeated-input interval dependency, not new numerical assumptions.
static I expPositive(I x) {
  if (x.lo>x.hi) fail();
  I left={x.lo,x.lo}; I right={x.hi,x.hi};
  I lower=expPositiveRaw(left); I upper=expPositiveRaw(right);
  I out={lower.lo,upper.hi}; return out;
}
static I logTight(I x) {
  if (x.lo<S || x.lo>x.hi) fail();
  I left={x.lo,x.lo}; I right={x.hi,x.hi};
  I lower=logPos(left); I upper=logPos(right);
  I out={lower.lo,upper.hi}; return out;
}
static I squareI(I x) { return mul(x,x); }
static I inverseI(I x) { return divI(unit(),x); }
static I sqrtInterval(I x) {
  if (x.lo>x.hi || x.hi>16*S) fail();
  U n[2]={mulU(x.lo,S),mulU(x.hi,S)};
  U result[2]; unsigned i=0;
  while (i<2) {
    U lo=0; U hi=4*S;
    while (lo<hi) {
      U mid=lo+(hi-lo)/2+1;
      if (mulU(mid,mid)<=n[i]) lo=mid; else hi=mid-1;
    }
    result[i]=lo; i=i+1;
  }
  if (mulU(result[1],result[1])!=n[1]) result[1]=addU(result[1],1);
  I out={result[0],result[1]}; return out;
}
static void emitU(U x) {
  uint64_t words[8]; unsigned i=0;
  while (i<8) { words[i]=(uint64_t)(x>>(64*i)); i=i+1; }
  if (fwrite(words,8,8,stdout)!=8) fail();
}
static void emitI(I x) { emitU(x.lo); emitU(x.hi); }
static I piBox,m0Box,gaussianBox,peakBox,sqrtPi,sqrt2Alpha;
static I alphaBox,dBox,deltaBox,smoothingBox;

static void initializeConstants() {
  // Generic mathematical pi input bounds, to be justified independently in Lean.
  I pl=rat(3141592653589793238ULL,1000000000000000000ULL);
  I ph=rat(3141592653589793239ULL,1000000000000000000ULL);
  piBox={pl.lo,ph.hi};
  alphaBox=rat(601,5000); dBox=rat(3681,10000); deltaBox=rat(3599,10000);
  m0Box=sqrtInterval(add(unit(),mul(rat(2,3),sqrtInterval(rat(6,5)))));
  gaussianBox=divN(sqrtInterval(divI(piBox,rat(601,2500))),2);
  peakBox=expNeg(divN(add(unit(),logTight(mul(rat(6,1),rat(601,2500)))),6));
  sqrtPi=sqrtInterval(piBox); sqrt2Alpha=sqrtInterval(mul(rat(2,1),alphaBox));
  I hstar=positiveSub(rat(3000000000000ULL,1),unit());
  smoothingBox=divI(rat(1,2),squareI(positiveSub(unit(),inverseI(hstar))));
}

static I rightRawCap(I t,I T) {
  I five=mul(divI(mul(mul(piBox,m0Box),rat(529,1000)),mul(rat(2,1),deltaBox)),
    mul(squareI(add(unit(),divI(mul(rat(2,1),deltaBox),t))),
      expPositive(divI(mul(mul(rat(2,1),deltaBox),rat(289,500)),t))));
  I six=add(mul(divI(rat(529,1000),mul(mul(rat(5,1),deltaBox),expPositive(deltaBox))),
      squareI(add(unit(),divI(deltaBox,t)))),
    divI(mul(rat(121,200),expNeg(mul(rat(2,1),deltaBox))),squareI(t)));
  I vertical=expPositive(mul(mul(rat(2,1),alphaBox),squareI(divI(add(unit(),divI(deltaBox,t)),T))));
  I first=divI(add(five,divI(mul(mul(six,piBox),m0Box),T)),mul(rat(4,1),alphaBox));
  I second=divI(mul(six,sqrtPi),mul(mul(rat(8,1),alphaBox),sqrt2Alpha));
  I V=mul(mul(mul(rat(8,1),alphaBox),vertical),add(first,second));
  return mul(V,squareI(t));
}
static I leftRawCap(I t,I T) {
  I a1=rat(611,1000); I eps=rat(1,10000); I eta=rat(7,10000);
  I m1=add(divI(rat(6,1),squareI(piBox)),divI(rat(131,125),t));
  I m2=add(add(divI(mul(mul(piBox,m0Box),rat(31,50)),t),divI(mul(rat(6,1),m0Box),mul(piBox,T))),
    divI(mul(mul(piBox,m0Box),rat(131,125)),mul(T,t)));
  I scale=mul(mul(a1,expPositive(divN(t,6))),t);
  I r=divI(rat(1461,1000),scale);
  I J=add(add(rat(373,200),mul(divI(rat(2,1),t),rat(1273,2000))),divI(rat(129,250),squareI(t)));
  I C=add(mul(m1,J),mul(m2,peakBox));
  I G=add(mul(m1,gaussianBox),m2);
  I mixed=add(mul(add(unit(),eta),C),mul(mul(add(unit(),inverseI(eta)),squareI(r)),G));
  I mainTerm=mul(mul(mul(add(unit(),eps),squareI(scale)),mul(T,t)),mixed);
  I unitTerm=mul(mul(add(unit(),inverseI(eps)),T),gaussianBox);
  I omega=expPositive(divI(alphaBox,mul(rat(2,1),squareI(T))));
  return mul(mul(rat(2,1),omega),add(mainTerm,unitTerm));
}
static void heightPair(I t,I *c,I *D) {
  I T=expPositive(t); I left=leftRawCap(t,T); I right=rightRawCap(t,T);
  I ll=logTight(left); I lr=logTight(right);
  I width=add(rat(1,2),divI(deltaBox,t));
  I theta=divI(add(rat(1,8),divI(add(dBox,deltaBox),t)),width);
  if (theta.hi>S) fail();
  I exponent=add(mul(theta,ll),mul(positiveSub(unit(),theta),lr));
  I prefactor=divI(mul(mul(smoothingBox,expPositive(mul(rat(2,1),alphaBox))),t),mul(mul(rat(2,1),piBox),dBox));
  *c=mul(prefactor,expPositive(exponent));
  *D=divI(positiveSub(ll,lr),width);
}
static I expNegAny(I x) {
  if (x.lo>x.hi) fail();
  unsigned shifts=0;
  while (x.hi>64*S) {
    x=divN(x,2); shifts=shifts+1; if (shifts>64) fail();
  }
  I value=expNeg(x);
  while (shifts>0) { value=mul(value,value); shifts=shifts-1; }
  return value;
}
static I paired(I D,unsigned L) {
  I Lbox=rat(L,1);
  if (D.hi>=Lbox.lo) fail();
  I difference=positiveSub(Lbox,D);
  I e=expNegAny(divN(difference,8));
  return add(e,divI(mul(Lbox,positiveSub(unit(),e)),difference));
}
