// Fixed-point kernels from finite.cpp; the log range is enlarged to 2^28.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using Z=__int128_t;
constexpr Z S=Z(1)<<56;
#ifndef LIMIT
#define LIMIT 256000000
#endif
constexpr int N=LIMIT;
void require(bool b){if(!b) std::abort();}
Z series(Z z){
    Z zz=z*z/S, q=z, a=0;
    for(int j=1;j<=39;j+=2){a+=q/j; q=q*zz/S;}
    return 2*a;
}
Z logfp(Z a){
    static const Z l2=series(S/3);
    require(a>=S);
    int k=0; while(a>=2*S){a>>=1;k++;}
    require(k<=27);
    return k*l2+series((a-S)*S/(a+S));
}
struct I{Z lo,hi;};
I add(I a,I b){return {a.lo+b.lo,a.hi+b.hi};}
I sub(I a,I b){return {a.lo-b.hi,a.hi-b.lo};}
Z ab(Z a){return a>=0?a:-a;}
Z ab(I a){return std::max(ab(a.lo),ab(a.hi));}
Z up(Z a,Z b){return (a+b-1)/b;}
I logi(int a){Z v=logfp(Z(a)*S);return {v,v+4096};}
I llogi(I a){return {logfp(a.lo),logfp(a.hi)+4096};}
struct State{I r,w,q,m,b;};
State acc(State a,int p){
    Z u=S/p, v=series(S/(Z(2)*p-1)), h=logfp(Z(p)*S), d=Z(p)*(p-1);
    Z m=0, d0=Z(p)*p, j=2;
    for(;d0<=S;d0*=p,j++) m+=S/(j*d0);
    return {add(a.r,{u,u+1}),add(a.w,{h/p,(h+4096)/p+1}),
            add(a.q,{v,v+128}),add(a.m,{m,m+j}),
            add(a.b,{h/d,(h+4096)/d+1})};
}
#include <array>
constexpr int first=900000, top=350;
int clocked[4][top+1];
int bin(Z numerator,Z denominator){
    require(numerator>=0 && denominator>0);
    return (int)std::min<Z>(top,numerator/denominator);
}
void inspect(State s,I G,I M,I B,I l,I r,int right){
    I zz[2],ww[2],rr[2],L[2]={l,r};
    for(int k=0;k<2;k++){
        I y=llogi(L[k]);
        ww[k]=add(sub(s.w,L[k]),B);
        rr[k]=sub(sub(s.r,y),M);
        zz[k]=sub(sub(s.q,y),G);
    }
    require(2*ww[0].hi<l.lo && 3*rr[0].hi<S && 3*zz[0].hi<S);
    Z zp=std::max<Z>(0,zz[0].hi),zm=std::max<Z>(0,-zz[1].lo);
    require(zp<S && zm<S && r.hi<20*S);
    int buckets[4]={};
    for(int k=0;k<2;k++){
        require(ab(ww[k])<S/16 && ab(rr[k])<S/512 && ab(zz[k])<S/512);
        Z p2=up(L[k].hi*L[k].hi,S),p3=up(p2*L[k].hi,S);
        Z pp=1000*std::max<Z>(0,zz[k].hi)*p3;
        Z pm=1000*std::max<Z>(0,-zz[k].lo)*p3;
        buckets[0]=std::max(buckets[0],bin(1000*ab(ww[k])*p2,S*S));
        buckets[1]=std::max(buckets[1],bin(1000*ab(rr[k])*p3,S*S));
        buckets[2]=std::max({buckets[2],bin(pm,S*(S-zm)),bin(pp,S*S)}); // P
        buckets[3]=std::max({buckets[3],bin(pp,S*(S-zp)),bin(pm,S*S)}); // Q
    }
    for(int j=0;j<4;j++)clocked[j][buckets[j]]=right;
}
int main(){
    std::vector<unsigned char> is(N+1,1);
    is[0]=is[1]=0;
    for(int p=2;p<=N/p;p++)if(is[p])
      for(int j=p*p;j<=N;j+=p)is[j]=0;
    std::vector<int> primes;
    State a{};
    for(int p=2;p<=N;p++)if(is[p]){primes.push_back(p);a=acc(a,p);}
    int n=1000000;Z h=0;
    for(int j=1;j<=n;j++)h+=S/j;
    I Ln=logi(n);
    I G={h-Ln.hi-up(S,2*n),h+n-Ln.lo-S/(2*n)+up(S,Z(n)*n)};
    I lN=logi(N);
    I M=sub(G,add(a.m,{93*S*S/(200*Z(N)*lN.hi),up(1004*S*S,2000*Z(N)*lN.lo)}));
    I B=add(G,add(a.b,{997*S/(Z(1000)*N),up(1003*S,Z(1000)*N)}));
    int prev=2;
    a=acc(State{},2);
    I lp=logi(first);
    for(int p:primes)if(p!=2){
        if(p>first){
            I rp=logi(p);
            inspect(a,G,M,B,lp,rp,p);
            lp=rp;
        }
        a=acc(a,p);prev=p;
    }
    require(prev<N);
    inspect(a,G,M,B,lp,lN,N);
    for(int j=0;j<4;j++)
        for(int c=top-1;c>=1;c--)clocked[j][c]=std::max(clocked[j][c],clocked[j][c+1]);
    printf("c/1000; finite inclusive onsets for (w,r,relative P,relative Q); N means no finite segment.\n");
    for(int c=300;c>=45;c--)
        if(c%5==0 || (c<=95 && c>=45)){
            printf("%d",c);
            for(int j=0;j<4;j++)printf(" %d",std::max(first,clocked[j][c]));
            puts("");
        }
    printf("prime count at %d: %zu\n",N,primes.size());
}

