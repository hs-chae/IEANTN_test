#include <cstdint>
#include <cstdio>
#include <vector>
#include <cstdlib>
using I=int64_t;
// S(v)=v-1 minus composites <=v whose least prime factor has been processed.
// Two arrays are used for the distinct v=floor(n/i).
I prime_count(I n){
  I r=0;
  while((r+1)*(r+1)<=n)++r;
  std::vector<I> lo(r+1),hi(r+1);
  for(I j=1;j<=r;j++){lo[j]=j-1;hi[j]=n/j-1;}
  auto at=[&](I v)->I&{return v<=r?lo[v]:hi[n/v];};
  for(I p=2;p<=r;p++)if(lo[p]>lo[p-1]){
    const I c=lo[p-1],q=p*p;
    for(I j=1;j<=r && n/j>r && n/j>=q;j++)hi[j]-=at(n/j/p)-c;
    for(I v=r;v>=q;v--)lo[v]-=lo[v/p]-c;
  }
  return hi[1];
}
int main(int argc,char**argv){
  for(int i=1;i<argc;i++){
    I x=strtoll(argv[i],nullptr,10);
    if(x<2 || x>40000000000LL)std::abort();
    printf("%lld %lld\n",(long long)x,(long long)prime_count(x));
  }
}
