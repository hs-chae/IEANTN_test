// Fixed-point certificate for prime reciprocals and two Euler products.
// Output is an ordinary executable certificate check, not a kernel theorem.
// Supply last x, numerator k in k/1000, first x, optional relative mesh divisor.
#define LIB_BRIDGE
#include "bridge.cpp"
#include <thread>
#include <atomic>
#include <limits>
using I=__int128_t;
struct Bounds{W l,r;};
Bounds lograt(W x,W unit){
 unsigned k=0;
 while(unit<=x/2){unit*=2;++k;}
 W l=W(k)*logseries(SCALE/3)+logseries(W(SCALE)*(x-unit)/(x+unit));
 return {l,l+W(k+1)*300};
}
Bounds loglogi(U x){
 auto l=lograt(x,1);
 return {lograt(l.l,SCALE).l,lograt(l.r,SCALE).r};
}
std::pair<I,I> gamma_constant(){
 constexpr U n=1000000;
 U hm=0;
 for(U j=1;j<=n;++j)hm+=SCALE/j;
 auto l=lograt(n,1);
 I gm=I(hm)-I(l.r)-(SCALE/(2*n)+1);
 I gp=I(hm+n)-I(l.l)-SCALE/(2*n)+SCALE/n/n+1;
 return {gm,gp};
}
void add_power(U p,U &km,U &kerr){
    W power=W(p)*p;
    for(U j=2;power<=SCALE;++j,power*=p){
       km+=SCALE/(power*j);
       ++kerr;
    }
    kerr+=2;
}
std::pair<I,I> mertens_constant(bool tight=false){
 constexpr U N=10000000;
 auto [gm,gp]=gamma_constant();
 U km=0,kerr=0;
 for(U p:primes_in(2,N))add_power(p,km,kerr);
 if (tight)
   return {gm-km-kerr-I(W(SCALE)*296/100000000000ULL)-1,
           gp-km-I(W(SCALE)*289/100000000000ULL)};
 return {gm-km-kerr-SCALE/(2*N)-1,gp-km};
}

struct Point{U x,s,n;};
#ifndef LIB_MFINITE
int main(int argc,char**argv){
 if(argc!=4&&argc!=5)return 2;
 U top=std::stoull(argv[1]), k=std::stoull(argv[2]),lo=std::stoull(argv[3]);
 U mesh=argc==5 ? std::stoull(argv[4]) : 40000;
 if(!mesh||top>300000000000ULL||top<lo||lo<100||k<5||k>500)return 2;
 init();
 auto [ml,mu]=mertens_constant();
 constexpr U width=1ULL<<23;
 U nb=top/width+1;
 std::vector<std::vector<Point>> blocks(nb);
 std::vector<std::pair<U,U>> totals(nb);
 std::atomic<U> task(0);
 std::vector<std::thread> threads;
 for(int w=0;w<8;++w)threads.emplace_back([&](){
   for(U b;(b=task++)<nb;){
     U start=std::max<U>(2,b*width),end=std::min<U>((b+1)*width-1,top);
     if(start>end)continue;
     auto ps=primes_in(start,end);
     auto &out=blocks[b];
     U n=0,s=0;
     auto advance=[&](U x){
       while(n<ps.size()&&ps[n]<=x){s+=SCALE/ps[n];++n;}
     };
     U prev=std::max(start,lo);
     if(prev<=end){
       for(U x=prev;;){
         advance(x);out.push_back({x,s,n});
         if(x==end)break;
         x=std::min(end,x+std::max<U>(1,x/mesh));
       }
     }
     advance(end);totals[b]={s,n};
   }
 });
 for(auto& t:threads)t.join();
 U s=0,n=0;
 Point a{};
 Bounds la{};
 U lastfail=0, firstgood=0, failures=0, good=0;
 for(U b=0;b<nb;++b){
   for(auto x:blocks[b]){
     x.s+=s;x.n+=n;
     auto lx=loglogi(x.x);
     if(a.x){
        auto l=lograt(x.x,1);
        W v=W(SCALE)*k/1000;
        for(int i=0;i<3;++i)v=v*SCALE/l.r;
        I dl=I(a.s)-I(lx.r)-mu, du=I(x.s+x.n)-I(la.l)-ml;
        // This reserves > 1/1000 relative headroom for exponentiation.
        I dec=I(v*999/1000);
        if(du>dec||dl-I(SCALE/(2*a.x)+1)<-dec){
          lastfail=x.x;++failures;firstgood=0;
        }else{
          if(!firstgood)firstgood=a.x;
          ++good;
        }
     }
     a=x;la=lx;
   }
   s+=totals[b].first;n+=totals[b].second;
 }
 std::cout<<"k/1000 "<<k<<" top "<<top<<" lo "<<lo<<" mesh "<<mesh
          <<" checks pass "<<good<<" fail "<<failures<<" last_failed_right "
          <<lastfail<<" verified_suffix "<<firstgood<<" primes "<<n<<"\n";
 return firstgood?0:1;
}

#endif
