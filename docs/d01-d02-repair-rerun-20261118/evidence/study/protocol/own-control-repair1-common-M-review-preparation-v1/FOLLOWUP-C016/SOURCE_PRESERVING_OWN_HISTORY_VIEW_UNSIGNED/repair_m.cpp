// Read snapshots from stdin: increasing pairs (last endpoint, next prime).
#include <vector>
#include <cstdint>
#include <cstdio>
#include <cassert>
#include <algorithm>
using Z=__int128_t;
const Z F=Z(1)<<62;
#ifndef LIMIT
#define LIMIT 2000000000
#endif
const int N=LIMIT;
struct Bound{Z lo,hi;};
void printz(Z z){
 if(z<0){std::putchar('-');z=-z;}
 char b[60];int i=0;do{b[i++]=char('0'+z%10);z/=10;}while(z);
 while(i)std::putchar(b[--i]);
}
void pairout(const char* name,Bound b){
 std::printf("%s ",name);printz(b.lo);std::putchar(' ');printz(b.hi);std::putchar(10);
}
int main() {
    const int K=100000000;
    std::vector<std::pair<int,int>> in;
    int a,b;
    while (scanf("%d%d",&a,&b)==2) {
        assert(a>=11 && b>a && b<=N && (in.empty()||a>in.back().first));
        in.emplace_back(a,b);
    }
    assert(!in.empty());
    int n=std::max(K,in.back().second);
    assert(n>=in.back().first);
    std::vector<bool> composite(n+1);
    for(int p=2;p*p<=n;++p) if(!composite[p])
        for(int j=p*p;j<=n;j+=p) composite[j]=true;
    for(auto [l,r]:in) {
        assert(r<=n);
        assert(!composite[l]&&!composite[r]);
        for(int j=l+1; j<r; ++j) assert(composite[j]);
    }
    const Z U=Z(1)<<100;
    Z powers=0,count=0,sp=0,cp=0;
    unsigned i=0;
    // Scan once: exact floor divisions for reciprocal and power sums.
    for(int p=2;p<=n;++p) if(!composite[p]) {
        if(p<=K) {
            Z q=Z(p)*p;
            int m=2;
            while(q<=U/m) {
                powers+=U/(q*m); ++count;
                q*=p; ++m;
            }
            // first omitted summand <1/U; remaining sum <2/U.
            count+=2;
        }
        sp+=F/p; ++cp;
        if(i<in.size() && p==in[i].first) {
            printf("%d %d ",p,in[i].second);printz(sp);putchar(' ');printz(cp);putchar(10);
            ++i;
        }
    }
    assert(i==in.size());
    pairout("S_powers_100m",Bound{powers,powers+count});
    return 0;
}
