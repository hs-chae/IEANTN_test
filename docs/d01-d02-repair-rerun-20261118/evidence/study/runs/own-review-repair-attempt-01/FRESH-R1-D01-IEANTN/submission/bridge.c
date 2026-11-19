/* Replay via bridge.py; all sign tests use integers. */
#include <assert.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
typedef uint64_t U;
typedef __uint128_t W;
#define END UINT64_C(100000000000)
#define S UINT64_C(10000000000000000)
#define EL UINT64_C(27182818284590452)
#define EU (EL+1)
#define START UINT64_C(38358837683)
#define BLOCK UINT64_C(1000000)
#define SQ 316227
static unsigned char seed[SQ+1], left[BLOCK/2+2], right[BLOCK/2+2];
static U ps[SQ], np=0;
static U fl(U x) { return (W)x*S/EU; }
static void make_seed(void){
  for(U j=2;j<=SQ;j++) if(!seed[j]){
    if(j>2) ps[np++]=j;
    if(j*j<=SQ) for(U i=j*j;i<=SQ;i+=j) seed[i]=1;
  }
}
static void sieve(U lo,U hi,unsigned char *v){
  assert(lo%2 && hi>=lo && hi-lo<=BLOCK+2);
  memset(v,0,(hi-lo)/2+1);
  for(U i=0;i<np;i++){
    U p=ps[i],z=p*p;
    if(z>hi) break;
    if(z<lo) z=((lo+p-1)/p)*p;
    if(!(z%2)) z+=p;
    for(U j=z;j<=hi;j+=2*p) v[(j-lo)/2]=1;
  }
}
int main(void){
  make_seed();
  U a=1644673232,b=632207037,q0=14111427770,checks=0;
  assert(SQ*(U)SQ<=END && (SQ+1)*(U)(SQ+1)>END);
  assert(START==2521*(U)15215723 && fl(START)==q0);
  for(U n=START;n<=END;n+=BLOCK){
    U h=n+BLOCK-1; if(h>END) h=END;
    U lo=n|1, r0=(q0+1)|1, r1=fl(h),lg;
    if(scanf("%" SCNu64,&lg)!=1) return 2;
    assert(lg < 300000000000000000ULL && r1>=r0);
    sieve(lo,h,left); sieve(r0,r1,right);
    U r=r0, d=(S+n-1)/n;
    for(U p=lo;p<=h;p+=2) if(!left[(p-lo)/2]){
      ++a;
      U q=fl(p);
      for(;r<=q;r+=2) b+=!right[(r-r0)/2];
      assert(a<10000000000ULL && b<10000000000ULL && r<=r1+2);
      if((W)EL*p*b <= (W)(lg+d*(p-n))*a*a){
        fprintf(stderr,"failed at %" PRIu64 "\n",p); return 1;
      }
      ++checks;
    }
    for(;r<=r1;r+=2) b+=!right[(r-r0)/2];
    q0=r1;
  }
  printf("Certified through %" PRIu64 "; %" PRIu64 " primes checked; final counts %" PRIu64 ", %" PRIu64 " at %" PRIu64 ", %" PRIu64 "\n",END,checks,a,b,END,q0);
  return 0;
}
