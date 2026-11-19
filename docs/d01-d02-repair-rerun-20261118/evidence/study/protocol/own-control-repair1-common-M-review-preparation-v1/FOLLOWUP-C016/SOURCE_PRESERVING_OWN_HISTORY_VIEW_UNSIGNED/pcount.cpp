// g++ -O3 pcount.cpp -o /work/pcount
#include <cstdio>
#include <cstdint>
#include <vector>
#include <cstdlib>
using u64=uint64_t;
u64 count(u64 n){
 u64 h=1;while((h+1)*(h+1)<=n)++h;
 std::vector<u64> v;
 for(u64 i=1,j;i<=n;i=j+1){v.push_back(n/i);j=n/v.back();}
 std::vector<u64> s;for(auto x:v)s.push_back(x-1);
 auto idx=[&](u64 x)->u64{return x<=h?v.size()-x:n/x-1;};
 for(u64 p=2;p<=h;++p){
  u64 sp=s[idx(p-1)];
  if(s[idx(p)]==sp)continue;
  for(u64 i=0;i<v.size()&&v[i]>=p*p;++i)s[i]-=s[idx(v[i]/p)]-sp;
 }
 return s[0];
}
int main(int argc,char**argv){for(int i=1;i<argc;++i){u64 n=strtoull(argv[i],0,10);printf("%llu %llu\n",(unsigned long long)n,(unsigned long long)count(n));}}
