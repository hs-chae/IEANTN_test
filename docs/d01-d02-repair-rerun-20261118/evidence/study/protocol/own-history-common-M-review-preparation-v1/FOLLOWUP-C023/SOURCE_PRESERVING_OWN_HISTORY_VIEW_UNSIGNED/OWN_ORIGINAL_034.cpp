// Near-baseline certificate with exact prime-jump locations.
// First argument is in thousandths (2278382000 means x=2278382).
#define LIB_MFINITE
#include "d02_mfinite.cpp"
// "w" mode: weighted prime sum, coefficient k/10^5, same onset unit.
int weighted(U lo,U hi,U kn){
 constexpr U unit=1000, N=10000000;
 if(lo<100*unit||hi*unit<lo||hi>N||kn>3000000)return 2;
 init();
 auto [bl,bu]=gamma_constant();
 auto ps=primes_in(2,N);
 std::vector<Bounds> logs;
 for(U p:ps){
   auto z=lograt(p,1);
   logs.push_back(z);
   U d=p*(p-1);
   bl+=I(z.l/d);
   bu+=I(z.r/d)+1;
 }
 bl+=I(W(SCALE)*997/(1000ULL*N));
 bu+=I(W(SCALE)*100301/(100000ULL*N))+1;
 W s=0,u=0;
 U lastfail=0,failures=0,pr=0,i=0;
 auto check=[&](U x){
   auto l=lograt(x,unit);
   W v=W(SCALE)*kn/10000000;
   for(int j=0;j<2;++j)v=v*SCALE/l.r;
   if(I(s)-I(l.r)+bl<-I(v)||I(u)-I(l.l)+bu>I(v)){lastfail=x;++failures;}
 };
 auto plateau=[&](U a,U b){
    if(b>lo){check(std::max(a,lo));check(b);}
 };
 for(U p:ps){
   if(p>hi)break;
   plateau(pr*unit,p*unit);
   s+=logs[i].l/p;u+=logs[i].r/p+1;
   ++i;pr=p;
 }
 plateau(pr*unit,hi*unit);
 check(hi*unit);
 std::cout<<"weighted/1000 "<<lo<<" "<<hi<<" "<<kn<<" fail "<<lastfail<<" "<<failures<<std::endl;
 return failures?1:0;
}
int main(int argc,char**argv){
 if(argc==5&&std::string(argv[1])=="w")return weighted(std::stoull(argv[2]),std::stoull(argv[3]),std::stoull(argv[4]));
 if(argc!=4)return 2;
 U lo=std::stoull(argv[1]),hi=std::stoull(argv[2]),kn=std::stoull(argv[3]);
 constexpr U unit=1000, start_sum=2260000000ULL;
 if(lo<100*unit||hi*unit<lo||hi>20000000||kn>2000000)return 2;
 init();
 auto [ml,mu]=mertens_constant(true);
 auto [gl,gu]=gamma_constant();
 U s=0,n=0,ks=0,ke=0;
 U lp=0,ls=0,np=0,ns=0;
 auto ok=[&](U x,bool product){
    if(x<(product?lo:std::max(lo,start_sum))) return true;
    auto z=lograt(x,unit);
    Bounds ll{lograt(z.l,SCALE).l,lograt(z.r,SCALE).r};
    W v=W(SCALE)*kn/10000000;
    for(int k=0;k<3;k++)v=v*SCALE/z.r;
    I dl=I(s)-I(ll.r)-(product?gu:mu);
    I du=I(s+n)-I(ll.l)-(product?gl:ml);
    if(product){dl+=ks;du+=ks+ke;v-=v*v/(2*W(SCALE))+1;}
    return dl>=-I(v)&&du<=I(v);
 };
 auto check=[&](U x){
    if(x<lo)return;
    if(!ok(x,true)){lp=x;++np;}
    if(!ok(x,false)){ls=x;++ns;}
 };
 auto ps=primes_in(2,hi);
 auto plateau=[&](U a,U b){
   if(a>lo||b>lo)check(std::max(lo,a));
   if(a<start_sum&&start_sum<b)check(start_sum);
   if(b>lo)check(b);
 };
 for(U p:ps){
    plateau(n?unit*ps[n-1]:0,p*unit);
    s+=SCALE/p;++n;add_power(p,ks,ke);
 }
 plateau(n?unit*ps[n-1]:0,hi*unit);
 // Include the exact right value even if hi was a prime (or hi=lo).
 check(hi*unit);
 std::cout<<"exact/1000 "<<lo<<" "<<hi<<" "<<kn<<" product "<<lp<<" "<<np
          <<" sum "<<ls<<" "<<ns<<std::endl;
 return (lp||ls)?1:0;
}
