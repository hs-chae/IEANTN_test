// Native exact finite computation, not a formal verification of C++.
// Build g++ -std=c++17 -O3 -pthread finite_ram.cpp -o /work/finite_ram
// Run /work/finite_ram 1630650286564 8
#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <thread>
#include <vector>
using u64 = uint64_t; using u128 = __uint128_t;
constexpr u64 S=4096, CHUNK=(1U<<22), W=15015, Q=1ULL<<48;
constexpr u64 K=38358837682ULL;
std::vector<unsigned> bp;
std::vector<unsigned char> mask;
std::vector<u64> prefix_count;
u64 E, L2;
u64 min_floor_gap = UINT64_MAX;

u64 up(u128 p,u64 q) {
    u128 d=p/q+(p%q!=0);
    assert(d<(u128(1)<<64));
    return u64(d);
}
// e in [E/Q,(E+2)/Q], where E=floor(Q sum_{i=0}^{20}1/i!).
u64 lower_e() {
    u64 f=1;
    for(unsigned j=2;j<=20;++j) f*=j;
    u128 sum=0;
    u64 term=f;
    for(unsigned j=0;j<=20;++j) {sum+=term; term/=j+1;}
    return u64(sum*Q/f);
}
// 2 atanh(a/b), upper fixed-point bound. Requires 0<=a/b<=1/3.
u64 log_atanh(u64 a,u64 b) {
    assert(3*a<=b);
    u64 t=up(u128(a)*Q,b), t2=up(u128(t)*t,Q), v=t, z=0;
    for(unsigned i=0;i<20;++i) {
        z+=up(v,2*i+1);
        v=up(u128(v)*t2,Q);
    }
    return 2*z+1; // geometric tail < 1/Q
}
u64 log_integer(u64 n) {
    assert(n>0);
    unsigned k=63-__builtin_clzll(n);
    u64 b=1ULL<<k;
    return k*L2+log_atanh(n-b,n+b);
}
u64 qlower(u64 n) {return u64(u128(n)*Q/(E+2));}
bool positive(u64 n,u64 lx,u64 px,u64 py) {
    assert(n<(1ULL<<41) && px<(1ULL<<36) && py<=px && lx<(1ULL<<54));
    u128 left=u128(E)*n*py, right=u128(lx)*px*px;
    if(left<=right) return false;
    u128 margin=(left-right)/lx;
    if(margin<min_floor_gap) min_floor_gap=u64(margin);
    return true;
}
void start(u64 top) {
    u64 r=1; while((r+1)*(r+1)<=top) ++r;
    std::vector<unsigned char> is(r+1,1);
    is[0]=is[1]=0;
    for(unsigned p=2;p<=r;++p) if(is[p]) {
        bp.push_back(p);
        if(u64(p)*p<=r)
            for(u64 t=u64(p)*p;t<=r;t+=p) is[t]=0;
    }
    mask.resize(2*W);
    for(u64 i=0;i<W;++i) {
        auto v=2*i+1;
        mask[i]=mask[i+W]=v%3!=0 && v%5!=0 && v%7!=0 && v%11!=0 && v%13!=0;
    }
}
// Odd candidates in (lo,hi] with lo even. 'arr[i]' semantically tests
// primality of lo+1+2*i after all base primes are processed.
void sieve(u64 lo,u64 hi,std::vector<unsigned char>& arr) {
    assert(lo%2==0 && hi>=lo);
    u64 n=(hi-lo+1)/2;
    arr.resize(n);
    if(!n) return;
    u64 offset=(lo/2)%W;
    for(u64 i=0;i<n;i+=W) std::memcpy(arr.data()+i,mask.data()+offset,std::min(W,n-i));
    for(u64 p:bp) {
        if(p<=13) continue;
        if(p*p>hi) break;
        u64 j=std::max(p*p,((lo+p)/p)*p);
        if(!(j&1)) j+=p;
        if(j<=hi)
            for(u64 k=(j-lo-1)/2;k<n;k+=p) arr[k]=0;
    }
    if(lo==0) arr[0]=0;
    for(u64 p: {3,5,7,11,13}) if(lo<p && p<=hi) arr[(p-lo-1)/2]=1;
}
u64 mkprefix(u64 target,unsigned nthreads) {
    u64 top=((target+S-1)/S)*S, blocks=(top+CHUNK-1)/CHUNK;
    assert(top<(1ULL<<41));
    start(top);
    prefix_count.resize(top/S+1);
    std::atomic<u64> idx{0}, done{0};
    auto worker=[&]() {
        std::vector<unsigned char> arr;
        for(;;) {
            u64 j=idx.fetch_add(1);
            if(j>=blocks) break;
            u64 lo=j*CHUNK, hi=std::min(top,lo+CHUNK);
            sieve(lo,hi,arr);
            for(u64 b=lo;b<hi;b+=S) {
                const unsigned char* cell=arr.data()+(b-lo)/2;
                unsigned c=0;
                for(u64 i=0;i<S/2;++i) c+=cell[i];
                prefix_count[b/S+1]=c+(b==0); // count 2
            }
            u64 d=done.fetch_add(1)+1;
            if(d%32768==0) std::cout<<"sieve blocks finished "<<d<<"/"<<blocks<<std::endl;
        }
    };
    std::vector<std::thread> jobs;
    for(unsigned t=0;t<nthreads;++t) jobs.emplace_back(worker);
    for(auto& t: jobs) t.join();
    for(u64 i=1;i<prefix_count.size();++i) prefix_count[i]+=prefix_count[i-1];
    std::cout<<"sieved through "<<top<<" inclusive, pi="<<prefix_count.back()<<std::endl;
    assert(prefix_count.back()<(1ULL<<36));
    return top;
}
u64 checks=0;
// Check initial point and all prime jumps, for a closed real interval [lo,hi].
bool fine(u64 lo,u64 hi) {
    assert(lo<=hi);
    u64 x0=lo/S*S, y0=qlower(lo)/S*S, px=prefix_count[x0/S], py=prefix_count[y0/S];
    std::vector<unsigned char> as, bs;
    sieve(x0,hi,as); sieve(y0,qlower(hi),bs);
    u64 iy=0;
    auto test=[&](u64 x) {
        u64 y=qlower(x);
        while(iy<bs.size() && y0+1+2*iy<=y) py+=bs[iy++];
        ++checks;
        if(!positive(x, log_integer(x),px,py)) {
            std::cerr<<"failed sign at "<<x<<" with pi(x)="<<px<<", pi(y)="<<py<<std::endl;
            return false;
        }
        return true;
    };
    u64 ix=0;
    while(ix<as.size()&&x0+1+2*ix<=lo) px+=as[ix++];
    if(!test(lo)) return false;
    for(;ix<as.size();++ix) if(as[ix]) {
        ++px;
        if(!test(x0+1+2*ix)) return false;
    }
    return true;
}
int main(int argc,char** argv) {
    if(argc<2) return 2;
    u64 top=std::strtoull(argv[1],nullptr,10);
    unsigned nt=argc>2?unsigned(std::strtoul(argv[2],nullptr,10)):8;
    assert(top>K && top<=1630650286564ULL && 1<=nt && nt<=8);
    E=lower_e(); L2=log_atanh(1,3);
    const auto began=std::chrono::steady_clock::now();
    std::cout<<"target "<<top<<" threads "<<nt<<" E "<<E<<" L2 "<<L2<<std::endl;
    mkprefix(top,nt);
    u64 coarse=0, failures=0, next=K+1, lg0=0, lg=0, fl=0, fr=0;
    auto flush=[&]() {
        if(!fl) return true;
        const bool ok=fine(fl,fr);
        fl=fr=0;
        return ok;
    };
    while(next<top) {
        u64 a=next, b=std::min(top,(a/S+1)*S);
        u64 u=a>>20<<20;
        if (u!=lg0) {lg0=u; lg=log_integer(u);}
        u64 lx=lg+up(u128(a-u)*Q,u);
        auto px=prefix_count[(b+S-1)/S], py=prefix_count[qlower(a)/S];
        if(positive(a,lx,px,py)) {
            ++coarse;
            if(!flush()) return 1;
        } else {
            ++failures;
            if(!fl) fl=a;
            fr=b;
            if (fr-fl>=CHUNK && !flush()) return 1;
        }
        next=b;
    }
    if(top==K+1 && !fine(top,top)) return 1;
    if(!flush()) return 1;
    auto elapsed=std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now()-began).count();
    std::cout<<"SUCCESS closed real interval ["<<K+1<<","<<top<<"]\n"
         <<"coarse passed "<<coarse<<" refined cells "<<failures
         <<" fine comparison points "<<checks<<" milliseconds "<<elapsed<<std::endl;
    std::cout<<"directed integer G lower bound "<<min_floor_gap<<std::endl;
}
