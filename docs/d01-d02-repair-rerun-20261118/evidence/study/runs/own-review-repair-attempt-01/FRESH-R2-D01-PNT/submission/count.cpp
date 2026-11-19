#include <cstdint>
#include <iostream>
#include <vector>
#include <cassert>
using I=std::int64_t;
I pi(I n) {
    assert(n>=2 && n<=40000000000LL);
    I s=1; while ((s+1)*(s+1)<=n) ++s;
    std::vector<I> a(s+1),b(s+1);
    for(I j=1;j<=s;++j){a[j]=j-1;b[j]=n/j-1;}
    auto get=[&](I v){return v<=s?a[v]:b[n/v];};
    for(I p=2;p<=s;++p)if(a[p]>a[p-1]){
        I z=a[p-1];
        for(I j=1;j<=s && n/j>=p*p;++j) b[j]-=get(n/j/p)-z;
        for(I j=s;j>=p*p;--j)a[j]-=a[j/p]-z;
    }
    return b[1];
}
int main(){ for(I n:{14111427770LL,38358837682LL,38358837683LL})
    std::cout<<n<<" "<<pi(n)<<"\n";
}
