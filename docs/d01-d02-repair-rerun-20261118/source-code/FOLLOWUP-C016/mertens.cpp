// Integer-only certificate. g++ -O3 -std=c++17 mertens.cpp -o /work/mertens
#include <vector>
#include <cstdint>
#include <cstdio>
#include <cassert>
#include <algorithm>
using Z=__int128_t;
using U=__uint128_t;
const Z F=Z(1)<<62;
#ifndef LIMIT
#define LIMIT 2000000000
#endif
const int N=LIMIT;
const int LE=6510;
Z core(Z n,Z d){ // 1<=n/d<=2; one-sided error <210/F
 assert(d<=n&&n<=2*d&&d>0);
 Z t=(F*(n-d))/(n+d),v=t,r=0;
 Z t2=t*t/F;
 for(int j=1;j<=41;j+=2){r+=v/j; v=v*t2/F;}
 return 2*r;
}
Z ln2;
Z logscaled(Z n,Z d=1){ // inputs used below >=1, output lower fixed point
 assert(n>=d&&d>0);
 int k=0;
 while(n>=2*d){d*=2;++k;}
 assert(k<=30);
 return k*ln2+core(n,d);
}
struct Bound{Z lo,hi;};
Z absup(Bound x){return std::max(-x.lo,x.hi);}
struct Target{int k;int numer,denom;int lastbad=0,next=0;Z wt=0,err=0,rp=0,lq=0,np=0;};
void printz(Z z){
 if(z<0){std::putchar('-');z=-z;}
 char b[60];int i=0;do{b[i++]=char('0'+z%10);z/=10;}while(z);
 while(i)std::putchar(b[--i]);
}
void pairout(const char* name,Bound b){
 std::printf("%s ",name);printz(b.lo);std::putchar(' ');printz(b.hi);std::putchar(10);
}
int main(){
 ln2=core(2,1);
 std::vector<bool> composite(N+1,false);
 for(int p=2;p*p<=N;++p)if(!composite[p])
   for(int i=p*p;i<=N;i+=p)composite[i]=true;
 const int ng=1000000;
 Z harm=0;for(int j=1;j<=ng;++j)harm+=F/j;
 Z gbase=harm-logscaled(ng)-F/(2*ng);
 Z gerr=F/(Z(ng-1)*(ng-1))+1;
 Bound gam{gbase-(LE+1)-gerr,gbase+ng+gerr+1};
 Z bs=0,be=0,ms=0;int np=0;
 for(int p=2;p<=N;++p)if(!composite[p]){
   ++np;
   bs+=logscaled(p)/(Z(p)*(p-1)); be+=LE/(Z(p)*(p-1))+2;
   ms+=core(p,p-1)-F/p;
 }
 // gamma + total weighted powers, gamma - total log powers
 Bound B{gam.lo+bs+(997*F)/(Z(1000)*N), gam.hi+bs+be+(1004*F)/(Z(1000)*N)+1};
 Bound M{gam.lo-ms-Z(211)*np-F/(Z(2)*N)-1, gam.hi-ms+np};
 std::vector<Target> t;
 for(int form=0;form<3;++form){
   t.push_back({form,223,10000});
   for(int c:{300,200,150,120,100,90,80,75,60,50,45,43,40,34,30,25,23})
     if(c!=300||form==2)t.push_back({form,c,1000});
 }
 Target state{};state.np=0;Z theta=0;
 auto good=[&](const Target& s, Z L,Z ll,const Target& D){
   Bound d[3]={
     {D.lq-gam.hi-ll-(LE+1),D.lq+210*D.np-gam.lo-ll},
     {D.rp-M.hi-ll-(LE+1),D.rp+D.np-M.lo-ll},
     {D.wt+B.lo-L-LE,D.wt+D.err+B.hi-L}
   };
   Z b=F*s.numer/s.denom;
   for(int j=0;j<(s.k==2?2:3);++j)b=b*F/(L+LE);
   if(s.k==0)b-= ((b*b)/(2*F)+1);
   return absup(d[s.k])<=b;
 };
 auto check=[&](int p,Z L,Z ll){
   for(auto &s:t)
     if(!good(s,L,ll,state))s.lastbad=p,s.next=0;
 };
 for(int p=2;p<=N;++p)if(!composite[p]){
   Z L=logscaled(p);
   Z ll=L>=F?logscaled(L,F):0;
   if(p>=11)check(p,L,ll); // left
   theta+=L;state.wt+=L/p;state.err+=LE/p+2;state.rp+=F/p;state.lq+=core(p,p-1);++state.np;
   if(p>=11)check(p,L,ll); // right
   for(auto &s:t) {
     if(s.lastbad==p){s.wt=state.wt;s.err=state.err;s.rp=state.rp;s.lq=state.lq;s.np=state.np;}
     if(!s.next&&p>s.lastbad)s.next=p;
   }
 }
 Z LN=logscaled(N), LL=logscaled(LN,F);
 check(N,LN,LL);
 pairout("B3",B);pairout("M",M);pairout("gamma",gam);
 pairout("theta-anchor",Bound{theta,theta+LE*state.np});
 pairout("reciprocal-anchor",Bound{state.rp-M.hi-LL-(LE+1),state.rp+state.np-M.lo-LL});
 pairout("weighted-anchor",Bound{state.wt+B.lo-LN-LE,state.wt+state.err+B.hi-LN});
 printf("N %d count %d\n",N,(int)state.np);
 for(auto s:t){
   long long x=0;
   if(s.lastbad>11&&s.next>s.lastbad){
     long long l=1000LL*s.lastbad,r=1000LL*s.next;
     auto g=[&](long long x){Z L=logscaled(x,1000);return good(s,L,logscaled(L,F),s);};
     assert(g(r)); // actual evaluation using pre-next sums
     while(l<r){long long m=(l+r)/2;if(g(m))r=m;else l=m+1;}
     assert(g(r)); x=r;
   }
   printf("form %d coefficient %d/%d last uncertified endpoint %d next prime %d verified start numerator (denom 1000) %lld\n",
          s.k,s.numer,s.denom,s.lastbad,s.next,x);
 }
}
