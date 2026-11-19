// Integer-only segmented sieve and outward fixed-point Mertens verifier.
// Build: /usr/bin/g++ -O3 -std=c++17 finite.cpp -o /work/finite
// No prime data or mathematical libraries are read.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <inttypes.h>

using Z = __int128;
using U = uint64_t;
constexpr Z S=Z(1)<<56;
Z fl(Z a,Z b){ assert(b>0); return a/b-(a%b<0); }
Z ce(Z a,Z b){ assert(b>0); return a/b+(a%b>0); }
Z mul(Z a,Z b){Z c; if(__builtin_mul_overflow(a,b,&c))std::abort(); return c;}
struct I {
  Z l,r;
  explicit I(Z a=0):l(mul(a,S)),r(l){}
  I(Z a,Z b):l(a),r(b){assert(a<=b);}
};
I operator+(I a,I b){return I(a.l+b.l,a.r+b.r);}
I operator-(I a,I b){return I(a.l-b.r,a.r-b.l);}
I operator*(I a,I b){
  Z t[]={mul(a.l,b.l),mul(a.l,b.r),mul(a.r,b.l),mul(a.r,b.r)};
  return I(fl(*std::min_element(t,t+4),S),ce(*std::max_element(t,t+4),S));
}
I rdiv(Z a,Z b){Z n=mul(a,S);return I(fl(n,b),ce(n,b));}
I divide(I a,Z b){return I(fl(a.l,b),ce(a.r,b));}
I sc(I a,Z b){if(b<0)return I(mul(a.r,b),mul(a.l,b));return I(mul(a.l,b),mul(a.r,b));}
I maxabs(I a){Z b=std::max(-a.l,a.r);assert(b>=0);return I(b,b);}
I logZ(I z) { // 2*atanh(z)
  assert(z.l>=0 && z.r<=S/3+1);
  I t=z,zz=z*z,y;
  for(int k=0;k<30;k++){y=y+divide(t,2*k+1);t=t*zz;}
  // positive omitted series <= 2*(1/3)^61/(1-1/9) < 1/S.
  return sc(y,2)+I(0,1);
}
const I ln2=logZ(rdiv(1,3));
I lnratio(Z n,Z d) { // ln(n/d), n,d positive, n>=d
  assert(n>=d && d>0);
  int k=0;
  while(2*d<=n){d*=2;k++;}
  return sc(ln2,k)+logZ(rdiv(n-d,n+d));
}
I lnU(U n){return lnratio(n,1);}
I lnI(I a){
  assert(a.l>=S);
  return I(lnratio(a.l,S).l,lnratio(a.r,S).r);
}
I logp(U p){return logZ(rdiv(1,2*p-1));}
I gamma(){
  constexpr U m=1000000;
  Z h=0; for(U k=1;k<=m;k++)h+=S/k;
  // Composite trapezoid remainder in the limit is in [0,m^-2].
  return I(h,h+m)-lnU(m)-rdiv(1,2*m)+I(0,rdiv(1,m*m).r);
}
struct Sample{U n; I s,q,t,L;};
struct Sieve {
  const U N;
  std::vector<U> base;
  std::vector<uint8_t> comp;
  U low=3,hi=1;
  size_t idx=0;
  explicit Sieve(U n):N(n) {
    U m=1; while(m+1<=N/(m+1))++m;
    std::vector<uint8_t> a(m+1);
    for(U p=2;p<=m;p++)if(!a[p]){
      if(p>2)base.push_back(p);
      for(U j=p*p;j<=m;j+=p)a[j]=1;
    }
  }
  bool load(){
    low=hi+2;
    if(low>N)return false;
    constexpr U size=1<<19;
    hi=std::min(low+2*(size-1),N|1);
    comp.assign((hi-low)/2+1,0);
    for(U p:base){
      if(p*p>hi)break;
      U j=std::max(p*p,(low+p-1)/p*p);
      if(!(j&1))j+=p;
      for(;j<=hi;j+=2*p)comp[(j-low)/2]=1;
    }
    idx=0;return true;
  }
  U next(){
    if(hi==1){hi=1; idx=1; load(); return 2;}
    while(true){
      while(idx<comp.size()){
        size_t k=idx++;
        if(!comp[k]){U p=low+2*k;return p<=N?p:N+1;}
      }
      if(!load())return N+1;
    }
  }
};

int main(int argc,char**argv){
  U N=3584912847ULL, rate=50000;
  if(argc>1)N=std::strtoull(argv[1],nullptr,10);
  if(argc>2)rate=std::strtoull(argv[2],nullptr,10);
  assert(N>=300000 && N<=30000000000ULL && rate>=10000 && rate<=1000000);
  const U cut=std::min(N,U(1<<26));
  std::vector<U> cuts={300000,500000,750000,912560,1000000,1500000,2000000,
     2278382,2278383,3000000,4000000,5000000,6000000,8000000,10000000,
     15000000,20000000,30000000,50000000,75000000,100000000,150000000,
     250000000,500000000,1000000000,2000000000,4000000000ULL,
     8000000000ULL,16000000000ULL};
  cuts.erase(std::upper_bound(cuts.begin(),cuts.end(),N),cuts.end());
  if(cuts.back()!=N)cuts.push_back(N);
  size_t edge=0;
  std::vector<Sample> rec;
  Sieve primes(N);
  U p=primes.next(),a=2;
  I s,q,t,D,la=lnU(2);
  U primecount=0;
  while(true){
    U n;
    if(a<32768)n=a;     // exact log(p) for small primes
    else n=std::min(N,std::min(cuts[edge],a+std::max(U(1),a/rate))); // real block ending at n
    assert(n>=a);
    I ln= a==n?la:lnU(n);
    Z h=0,pow2sum=0,pow2hi=0,dz=0; U m=0, nb=0;
    while(p<=n){
      U f=(U)S/p;
      h+=f; ++m; ++primecount;
      if(p<=4096) q=q+logp(p);
      else{
        // Floors of terms of orders 2,3,4. If a denominator is omitted
        // below then it exceeds S, so its floor is 0.
        if(p<(1u<<28))pow2sum+=(U)S/(2*p*p);
        if(p<(1u<<20))pow2sum+=(U)S/(3*p*p*p);
        if(p<(1u<<15))pow2sum+=(U)S/(4*p*p*p*p);
        pow2sum+=f;pow2hi+=4;
      }
      if(p<=cut){
        if(a==n){D=D+la*rdiv(1,p*(p-1));}
        else{dz+=(U)S/(p*(p-1));++nb;}
      }
      p=primes.next();
    }
    // For p>4096, positive log-series remainder beyond degree four is
    // <= 1/[5*p^5*(1-1/p)] per prime. A per-prime +1 unit fits it since
    // p>=4097. The global sharper bound is added once to q when sampling.
    q=q+I(pow2sum,pow2sum+pow2hi);
    I delta=I(h,h+m);
    s=s+delta;
    if(a==n)t=t+la*delta;
    else{
      // (ln a-1)*sum(1/p)+m/a is the linearization, and the concave
      // error lies between -(n-a)^2/(2*a^2)*sum(1/p) and zero.
      I u=(la-I(1))*delta+rdiv(m,a);
      I dr=rdiv(n-a,a);
      I err=divide(dr*dr*delta,2);
      t=t+u-I(0,err.r);
      D=D+I(la.l,ln.r)*I(dz,dz+nb);
    }
    if(n>=cuts[0]){
      // Tail for all p>4096: sum_{n>4096} 1/(5(1-1/4096)n^5)
      // <= [20(1-1/4096)4096^4]^-1 < 20/S.
      rec.push_back(Sample{n,s,q+I(0,20),t,ln});
    }
    if(n==N)break;
    if(n==cuts[edge])++edge;
    if(a<32768){a=n+1;la=lnU(a);}
    else{a=n;la=ln;}
  }
  // Use directly certified constants. M tail <=1/(2N), B3 tail <=
  // 2*(ln cut+1)/cut by sum <= integral of decreasing log(t)/t^2.
  I G=gamma();
  I M=G-(rec.back().q-rec.back().s)-I(0,rdiv(1,2*N).r);
  I B3=G+D+I(0,divide(sc(lnU(cut)+I(1),2),cut).r);
  std::printf("N=%" PRIu64 ", pi(N)=%" PRIu64 ", samples=%zu, rate=%" PRIu64 "\n",
              N,primecount,rec.size(),rate);
  constexpr U out=1000000; // report ceiling on 10^6 times the coefficient.
  size_t k=1; std::array<U,3> worst{}, cum{};
  std::vector<std::array<U,3>> all;
  std::array<U,31> badP={},badS={},badT={};
  I ll=lnI(rec[0].L);
  for(size_t j=1;j<rec.size();++j){
    auto x=rec[j-1],y=rec[j];
    assert(x.n<y.n);
    I lu=lnI(y.L), L2=y.L*y.L, L3=L2*y.L;
    auto envelope=[](I A,I B,I f,I g,I c){return I((A-g-c).l,(B-f-c).r);};
    I qp=maxabs(envelope(x.q,y.q,ll,lu,G));
    I sp=maxabs(envelope(x.s,y.s,ll,lu,M));
    I tp=maxabs(envelope(x.t,y.t,x.L,y.L,I(0)-B3));
    assert(qp.r<S);
    qp=rdiv(qp.r,S-qp.r);  // exp(a)-1 <= a/(1-a)
    std::array<I,3> v={qp*L3,sp*L3,tp*L2};
    for(int h=0;h<3;h++){
      U m=(U)ce(mul(v[h].r,out),S);
      worst[h]=std::max(m,worst[h]);
    }
    for(int z=1;z<=30;z++){
      const Z c=Z(z)*S/100;
      if(v[0].r>=c)badP[z]=y.n;
      if(v[1].r>=c)badS[z]=y.n;
      if(v[2].r>=c)badT[z]=y.n;
    }
    ll=lu;
    if(y.n==cuts[k]){
      std::printf("[%" PRIu64 ",%" PRIu64 "] : %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
                  cuts[k-1],cuts[k],worst[0],worst[1],worst[2]);
      all.push_back(worst);worst={};
      ++k;
    }
  }
  assert(k==cuts.size() && rec.back().n==N);
  std::puts("k/100 : last endpoint of a failed bin (0 if none), products, S0, S1:");
  for(int z=1;z<=30;z++)std::printf("%d : %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",z,badP[z],badS[z],badT[z]);
}
