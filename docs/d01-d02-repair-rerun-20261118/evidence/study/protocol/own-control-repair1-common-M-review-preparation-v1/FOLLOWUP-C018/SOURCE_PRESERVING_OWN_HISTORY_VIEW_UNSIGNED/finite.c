/* Exact fixed-point analytic/finite joins; see candidate.md.
 * Build: /usr/bin/gcc -O3 -std=c11 finite.c -o /work/finite
 * Run: /work/finite
 */
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
typedef uint64_t U;
typedef __uint128_t W;
typedef int64_t S;
#define SCALE (UINT64_C(1)<<56)
#define EPS UINT64_C(16384)
#define N 20000000
#define MINX 100000
#define K 1000000
static unsigned char notp[N+1];
static U updiv(W x,U y){return (x+y-1)/y;}
static U mul(U x,U y){return updiv((W)x*y,SCALE);}
static U series(U t){ // <= log((1+t/SCALE)/(1-t/SCALE))
  U s=0,v=t; U t2=(W)t*t/SCALE;
  for(unsigned k=1;k<=61;k+=2){s+=v/k;v=(W)v*t2/SCALE;}
  return 2*s;
}
static U lnr(U x,U y){ // 1<=x/y, x/y<=N+1; absolute upward slack EPS
  assert(x>=y && y>0);
  static U log2=0;
  if(!log2)log2=series(SCALE/3);
  U d=y; unsigned k=0;
  while(d<=x/2){d*=2;k++;}
  assert(k<=25);
  return k*log2+series((W)(x-d)*SCALE/((W)x+d));
}
static U power0(unsigned p,U* err){
  U s=0; W d=(W)p*p;
  for(unsigned k=2;d<=SCALE;k++,d*=p){s+=SCALE/(d*k);(*err)++;}
  (*err)+=2;
  return s;
}
static void sieve(void){
 notp[0]=notp[1]=1;
 for(unsigned p=2;p*p<=N;p++)if(!notp[p]){
   for(unsigned q=p*p;q<=N;q+=p)notp[q]=1;
 }
}
static U max(U a,U b){return a>b?a:b;}
static U mag(S a){return a<0?-a:a;}
static U absbox(S lo,S hi){return max(mag(lo),mag(hi));}
static U last[4][5];
static U witnesses[4][5];
static const unsigned marg[4][5]={
 {200,190,180,160,150}, {200,190,180,160,150}, {300,270,240,210,180}, {200,190,180,160,150}};
static void check(unsigned a,unsigned b,U s0,U w0,U s1,U w1,S m0,S m1,S b0,S b1,U a0,U aerr,S g0,S g1){
 if(b<MINX)return;
 if(a<MINX)a=MINX;
 if(a>b)return;
 U la=lnr(a,1),lb=lnr(b,1)+EPS;
 U lla=lnr(la,SCALE),llb=lnr(lb,SCALE)+EPS;
 S lo=(S)s0-m1-(S)llb, hi=(S)(s0+w0)-m0-(S)lla;
 S ql=(S)(s0+a0)-g1-(S)llb,qh=(S)(s0+w0+a0+aerr)-g0-(S)lla;
 U ep=mag(ql),eq=mag(qh);
 assert(ep<SCALE/1002 && eq<SCALE/1002);
 U errs[4]={absbox(lo,hi),max(qh>0?updiv((W)eq*1001,1000):0,ql<0?ep:0),
            absbox((S)s1+b0-(S)lb,(S)(s1+w1)+b1-(S)la),
            max(ql<0?updiv((W)ep*1001,1000):0,qh>0?eq:0)};
 // Also try genuine violations at the left integer of each cell.
 U ua=la+EPS, ula=lnr(ua,SCALE)+EPS;
 S lt=(S)s0-m1-(S)ula,ht=(S)(s0+w0)-m0-(S)lla;
 S qt=(S)(s0+a0)-g1-(S)ula;
 S lw=(S)s1+b0-(S)ua,hw=(S)(s1+w1)+b1-(S)la;
 U qa=qt>0?(U)qt:qh<0?mag(qh):0;
 U wq=qa-(qa?mul(qa,qa)/2+1:0);
 U lows[4]={lt>0?lt:ht<0?-ht:0, wq, lw>0?lw:hw<0?-hw:0, wq};
 for(unsigned i=0;i<4;i++){
  U z=mul(mul(errs[i],lb),lb);
  if(i!=2)z=mul(z,lb);
  U wd=(W)lows[i]*la/SCALE;wd=(W)wd*la/SCALE;
  if(i!=2)wd=(W)wd*la/SCALE;
  for(unsigned j=0;j<5;j++){
   if((W)z*1000>(W)marg[i][j]*SCALE)last[i][j]=b;
   if((W)wd*1000>(W)marg[i][j]*SCALE)witnesses[i][j]=a;
  }
 }
}
int main(void){
 sieve();
 U g=0;
 for(unsigned k=1;k<=K;k++)g+=SCALE/k;
 U l=lnr(K,1);
 S g0=(S)g-l-EPS-updiv(SCALE,2*K);
 S g1=(S)g+K-l-SCALE/(2*K)+updiv(SCALE,(U)K*K);
 U a0=0,e0=0,a1=0,e1=0;
 for(unsigned p=2;p<=N;p++)if(!notp[p]){
  a0+=power0(p,&e0);
  U d=(U)p*(p-1);
  a1+=lnr(p,1)/d;e1+=1+updiv(EPS,d);
 }
 S m0=g0-(S)(a0+e0+updiv((W)150*SCALE,UINT64_C(100000000000))),m1=g1-(S)(a0+(W)138*SCALE/UINT64_C(100000000000));
 S b0=g0+(S)(a1+(W)997*SCALE/(1000ULL*N)),b1=g1+(S)(a1+e1+updiv((W)1004*SCALE,1000ULL*N));
 printf("denominator %" PRIu64 "; M [%" PRId64 ",%" PRId64 "]; B3 [%" PRId64 ",%" PRId64 "]\n",(U)SCALE,m0,m1,b0,b1);
 U s0=0,w0=0,s1=0,w1=0; a0=0;e0=0;
 unsigned a=2;
 for(unsigned p=2;p<=N;p++)if(!notp[p]){
  if(p>2)check(a,p,s0,w0,s1,w1,m0,m1,b0,b1,a0,e0,g0,g1);
  s0+=SCALE/p;w0++;a0+=power0(p,&e0);
  s1+=lnr(p,1)/p;w1+=1+updiv(EPS,p);
  a=p;
 }
 check(a,N,s0,w0,s1,w1,m0,m1,b0,b1,a0,e0,g0,g1);
 for(unsigned i=0;i<4;i++){
  for(unsigned j=0;j<5;j++)printf("%u %u last possibly failing cell ends at %" PRIu64 "; violation witness %" PRIu64 "\n",i,marg[i][j],last[i][j],witnesses[i][j]);
 }
}
