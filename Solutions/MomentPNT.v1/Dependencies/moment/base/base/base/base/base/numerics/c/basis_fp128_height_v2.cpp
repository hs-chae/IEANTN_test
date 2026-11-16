// Copyright (c) 2026 IEANTN contributors. Apache-2.0.
// New research algorithm, separate from the frozen Scoped Winner migration.
// Positive directed fixed-point intervals. No computed outputs are embedded.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned _BitInt(512) U;
struct I { U lo; U hi; };
static const U S = ((U)1) << 128;
static const U MAXU = (U)(-1);
static I ln2;

static void fail() { fputs("basis arithmetic/domain failure\n",stderr); exit(3); }
static U addU(U a,U b) { if (MAXU-a<b) fail(); return a+b; }
static U mulU(U a,U b) { if (a!=0 && MAXU/a<b) fail(); return a*b; }
static U ceilDiv(U a,U b) { if (b==0) fail(); return addU(a/b,a%b!=0); }
static I rat(U n,U d) { U a=mulU(n,S); I r={a/d,ceilDiv(a,d)}; return r; }
static I unit() { I r={S,S}; return r; }
static I zero() { I r={0,0}; return r; }
static I add(I a,I b) { I r={addU(a.lo,b.lo),addU(a.hi,b.hi)}; return r; }
static I mul(I a,I b) { I r={mulU(a.lo,b.lo)/S,ceilDiv(mulU(a.hi,b.hi),S)}; return r; }
static I divI(I a,I b) {
  if (b.lo==0) fail();
  I r={mulU(a.lo,S)/b.hi,ceilDiv(mulU(a.hi,S),b.lo)}; return r;
}
static I divN(I a,unsigned n) {
  if (n==0) fail(); I r={a.lo/n,ceilDiv(a.hi,n)}; return r;
}
static I positiveSub(I a,I b) {
  I r={a.lo>b.hi?a.lo-b.hi:0,a.hi>b.lo?a.hi-b.lo:0}; return r;
}
static I expNeg(I x) {
  if (x.lo>x.hi || x.hi>64*S) fail();
  I z=divN(x,64);
  I p=unit();
  unsigned k=48;
  while (k>0) { p=positiveSub(unit(),divN(mul(z,p),k)); k=k-1; }
  I r={p.lo>0?p.lo-1:0,addU(p.hi,1)};
  k=0;
  while (k<6) { r=mul(r,r); k=k+1; }
  return r;
}
static I atanh2(I r) {
  if (r.lo>r.hi || r.hi>S/2) fail();
  I rr=mul(r,r);
  I term=r;
  I sum=zero();
  unsigned k=0;
  while (k<80) {
    sum=add(sum,divN(term,2*k+1)); term=mul(term,rr); k=k+1;
  }
  I result=add(sum,sum); result.hi=addU(result.hi,1); return result;
}
static I logPos(I x) {
  if (x.lo<S || x.lo>x.hi) fail();
  I m=x;
  unsigned k=0;
  while (m.lo>2*S) { m=divN(m,2); k=k+1; if (k>384) fail(); }
  if (m.hi>3*S) fail();
  I r=divI(positiveSub(m,unit()),add(m,unit()));
  return add(atanh2(r),mul(rat(k,1),ln2));
}
static U floorCube(U n) {
  U lo=0;
  U hi=4*S;
  while (lo<hi) {
    U m=lo+(hi-lo)/2+1;
    if (mulU(mulU(m,m),m)<=n) lo=m; else hi=m-1;
  }
  return lo;
}
static I cubeRoot(I x) {
  if (x.lo>x.hi || x.hi>16*S) fail();
  U a=floorCube(mulU(x.lo,mulU(S,S)));
  U n=mulU(x.hi,mulU(S,S));
  U b=floorCube(n);
  if (mulU(mulU(b,b),b)!=n) b=addU(b,1);
  I out={a,b}; return out;
}
static I gaussianCell(I left,I right,I width) {
  I q=rat(601,2500);
  return mul(width,mul(expNeg(mul(q,mul(left,left))),cubeRoot(right)));
}
int main() {
  ln2=atanh2(rat(1,3));
  I j0=zero(); I j1=zero(); I j2=zero();
  const unsigned prefix=4096;
  unsigned i=0;
  while (i<prefix) {
    I left=rat(5*prefix+i,6*prefix);
    I right=rat(5*prefix+i+1,6*prefix);
    j0=add(j0,gaussianCell(left,right,rat(1,6*prefix))); i=i+1;
  }
  const unsigned cells=32768;
  i=0;
  while (i<cells) {
    I left=rat(cells+15*i,cells);
    I right=rat(cells+15*(i+1),cells);
    I area=gaussianCell(left,right,rat(15,cells));
    I lr=logPos(right);
    j0=add(j0,area); j1=add(j1,mul(area,lr)); j2=add(j2,mul(area,mul(lr,lr)));
    i=i+1;
  }
  I q=rat(601,2500);
  I M=expNeg(divN(add(unit(),logPos(mul(rat(6,1),q))),6));
  I bq=mul(rat(256,1),q);
  I tail=divI(mul(expNeg(bq),add(bq,unit())),mul(rat(2,1),mul(q,q)));
  j0=add(add(j0,mul(rat(5,6),M)),tail); j1=add(j1,tail); j2=add(j2,tail);
  I result[3]={j0,j1,j2};
  uint64_t out[18];
  i=0;
  while (i<3) {
    out[6*i]=(uint64_t)result[i].lo; out[6*i+1]=(uint64_t)(result[i].lo>>64);
    out[6*i+2]=(uint64_t)(result[i].lo>>128);
    out[6*i+3]=(uint64_t)result[i].hi; out[6*i+4]=(uint64_t)(result[i].hi>>64);
    out[6*i+5]=(uint64_t)(result[i].hi>>128); i=i+1;
  }
  return fwrite(out,8,18,stdout)==18?0:2;
}
