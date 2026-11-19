// Exact finite verification: R(x)>0 for every real x in [lo,hi].
// One invocation per integer interval; neighbouring intervals MUST share endpoints.
#define LIB_COUNT
#include "d02_count.cpp"
#include <cassert>
#include <algorithm>
using W=__uint128_t;
constexpr U SCALE = 1ULL<<60, K=1ULL<<52, D=1000000000000000000ULL;
constexpr U EL=2718281828459045235ULL, EU=EL+1;
U logseries(U z){
 U v=z;
 U s=0;
 for(int i=0;i<40;i++){
   s+=2*v/(2*i+1);
   v=W(v)*z/SCALE*z/SCALE;
 }
 return s;
}
W logupper(U x){
 U base=1;unsigned k=0;
 while(base<=x/2){base*=2;++k;}
 return W(k)*(logseries(SCALE/3)+300)+logseries(W(SCALE)*(x-base)/(x+base))+300;
}
W flower(U x){
 return W(x)*((W(K)*(W(EL)*SCALE/D))/logupper(x));
}
U ylimit(U x){return W(x)*D/EU;}
std::vector<U> primes_in(U l,U r){
 std::vector<U> v;
 if(l>r)return v;
 if(l<=2&&2<=r)v.push_back(2);
 l=std::max<U>(l|1,3);
 if(l>r)return v;
 std::vector<unsigned char> cp((r-l)/2+1);
 for(int i:p){
   if(i==2)continue;
   if(U(i)*i>r)break;
   U q=std::max<U>(U(i)*i,(l+i-1)/i*i);
   if(!(q&1))q+=i;
   for(;q<=r;q+=2*i)cp[(q-l)/2]=1;
 }
 for(U i=0;i<cp.size();i++)if(!cp[i])v.push_back(l+2*i);
 return v;
}
bool interval(U l,U r){
 U a=count_prime(l-1), b=count_prime(ylimit(l-1));
 for(U s=l;s<=r;){
   U t=std::min(s+2097151,r), n=t+1-s;
   auto px=primes_in(s,t), py=primes_in(ylimit(s-1)+1,ylimit(t));
   std::vector<U> ey;
   for(U q:py)ey.push_back((W(q)*EU+D-1)/D);
   size_t i=0,j=0;
   auto B=[&](U x){while(j<ey.size()&&ey[j]<=x)++j; return b+j;};
   W fs=flower(s), ft=flower(t);
   auto ok=[&](U x,U a1){
      W f=(t>s?(fs*(t-x)+ft*(x-s))/(t-s):fs);
      return f*B(x)>W(a1)*a1*K;
   };
   // At segment start, and at all prime jumps; coverage through t+1
   // (excluding t+1) follows by monotonicity before the next integer.
   for(U u=s;u<=t;){
     U v=std::min(u+1023,t);
     size_t k=i;while(k<px.size()&&px[k]<=v)++k;
     if(!ok(u,a+k)){
       if(i==k||px[i]>u)if(!ok(u,a+i)) {std::cerr<<"FAIL "<<u<<"\n";return false;}
       for(;i<k;++i)if(!ok(px[i],a+i+1)){std::cerr<<"FAIL "<<px[i]<<"\n";return false;}
     }
     i=k;u=v+1;
   }
   a+=px.size();b+=py.size();s=t+1;
 }
 return true;
}
#ifndef LIB_BRIDGE
int main(int argc,char**argv){
 if(argc!=3)return 2;
 U lo=std::stoull(argv[1]),hi=std::stoull(argv[2]);
 if(lo<38358837683ULL||lo>hi||hi>100000000000ULL)return 2;
 init();
 // Sanity checks independent of any prime table.
 for(U a=4999990;a<=5000030;++a){
   if(count_prime(a)-count_prime(a-1)!=primes_in(a,a).size())return 3;
 }
 if(!interval(lo,hi))return 1;
 std::cout<<"OK "<<lo<<" "<<hi<<std::endl;
}

#endif
