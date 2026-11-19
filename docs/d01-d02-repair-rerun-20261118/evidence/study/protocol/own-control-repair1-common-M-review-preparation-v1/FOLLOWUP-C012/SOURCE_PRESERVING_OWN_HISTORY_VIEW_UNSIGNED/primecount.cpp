// Deterministic combinatorial prime counts, no input tables.
#include <cstdint>
#include <vector>
#include <iostream>
#include <cassert>
using Z=uint64_t;
Z pc(Z n){
 assert(n>=2 && n<=100000000000ULL);
 Z r=1;while((r+1)*(r+1)<=n)++r;
 Z m=n/(r+1);
 std::vector<Z> a(r+1),b(m+1);
 for(Z s=1;s<=r;++s)a[s]=s-1;
 for(Z i=1;i<=m;++i)b[i]=n/i-1;
 auto f=[&](Z t){if(t<=r)return a[t];assert(n/(n/t)==t);return b[n/t];};
 for(Z p=2;p<=r;++p)if(a[p]>a[p-1]){
  Z e=a[p-1],q=p*p;
  for(Z i=1;i<=m && i<=n/q;++i){Z v=f(n/i/p);assert(v>=e && b[i]>=v-e);b[i]-=v-e;}
  for(Z s=r;s>=q;--s){Z v=a[s/p];assert(v>=e && a[s]>=v-e);a[s]-=v-e;}
 }
 return b[1];
}
int main(){
 Z n;while(std::cin>>n)std::cout<<n<<" "<<pc(n)<<"\n";
}
