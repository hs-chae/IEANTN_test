// Exact Lehmer prime count for 0 <= x <= 10^11; no external prime table.
#include <cstdint>
#include <cmath>
#include <iostream>
#include <vector>
#include <unordered_map>
#include <stdexcept>
using U = uint64_t;
const int N=5000000, A=64, M=65536;
int pi_small[N+1], tab[A][M];
std::vector<int> p;
std::unordered_map<U,U> cache;
void init(){
 std::vector<bool> composite(N+1);
 for(int i=2;i<=N;++i){
   if(!composite[i]){
     p.push_back(i);
     if(i<=N/i) for(int j=i*i;j<=N;j+=i) composite[j]=true;
   }
   pi_small[i]=p.size();
 }
 for(int j=0;j<M;++j) tab[0][j]=j;
 for(int a=1;a<A;++a) for(int j=0;j<M;++j)
   tab[a][j]=tab[a-1][j]-tab[a-1][j/p[a-1]];
}
U root(U x,int k){
 // Float is only a search seed; final direction determined by exact powers.
 U r=std::pow((long double)x,1.0L/k);
 auto powk=[&](U v) {U z=1;for(int j=0;j<k;++j)z*=v;return z;};
 while(powk(r)>x)--r;
 while(powk(r+1)<=x)++r;
 return r;
}
U phi(U x,int a){
 if(!a||!x)return x;
 if(a<A&&x<M)return tab[a][x];
 if(x<=U(p[a-1]))return 1;
 if(x<=N&&x<U(p[a])*p[a])return 1+pi_small[x]-a;
 return phi(x,a-1)-phi(x/p[a-1],a-1);
}
U count_prime(U x){
 if(x<=N)return pi_small[x];
 auto it=cache.find(x);if(it!=cache.end())return it->second;
 int a=pi_small[root(x,4)], b=pi_small[root(x,2)], c=pi_small[root(x,3)];
 U sum=phi(x,a)+a-1;
 // Count semiprimes and triprimes, ordered by smallest factor.
 for(int i=a;i<b;++i){
   U q=x/p[i];
   sum-=count_prime(q)-i;
   if(i<c){
     int lim=pi_small[root(q,2)];
     for(int j=i;j<lim;++j)sum-=count_prime(q/p[j])-j;
   }
 }
 cache[x]=sum;return sum;
}
#ifndef LIB_COUNT
int main(){
 init();
 U x;
 while(std::cin>>x){if(x>100000000000ULL)throw std::out_of_range("x");
 std::cout<<x<<" "<<count_prime(x)<<std::endl;}
}
#endif
