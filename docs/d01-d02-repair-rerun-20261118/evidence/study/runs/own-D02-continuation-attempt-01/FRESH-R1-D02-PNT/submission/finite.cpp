#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using Z=__int128_t;
constexpr Z S=Z(1)<<56;
constexpr int N=64000000;
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
    require(k<=25);
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
// Inclusive onset, common reciprocal/product coefficient times 1000, weighted times 1000.
// Zero in a coefficient field means do not test that field.
struct Test{int64_t x1000; int r,w;};
Test ts[]={{912559999,0,300},{1000000000,0,297},{1530000000,0,250},
           {2278381900,-200,0},{2278382200,200,0},{2278395000,199,215},
           {3451810000,190,213},{3459000000,180,212},{3462000000,170,211},{3475000000,160,200},
           {5010000000,150,163},{7110000000,140,151},{7130000000,130,150},
           {8800000000,125,140},{13000000000,120,123},{14000000000,100,110},
           {18003000000,0,100},{18010000000,95,0},{18500000000,90,95},{30912000000,87,0},{30923000000,87,90},{33000000000,87,89},
           {38000000000,87,88},{50000000000,87,87}};
I log1000i(int64_t a){Z v=logfp(Z(a)*S/1000);return {v,v+4096};}
bool verify(State a,I G,I M,I B,I ll,I lr,int ir,int iw){
    // Check monotonicity of signed centered errors times L^k on the gap.
    // Endpoint tests use each endpoint's own power of L.
    I yl=llogi(ll),yr=llogi(lr);
    I wl=add(sub(a.w,ll),B),wr=add(sub(a.w,lr),B);
    I rl=sub(sub(a.r,yl),M),rr=sub(sub(a.r,yr),M);
    I ql=sub(sub(a.q,yl),G),qr=sub(sub(a.q,yr),G);
    require(2*wl.hi<ll.lo && 3*rl.hi<S && 3*ql.hi<S);
    Z z=std::max(ab(ql),ab(qr));
    require(z<S && ab(wl)<S && ab(wr)<S && ab(rl)<S && ab(rr)<S && lr.hi<18*S);
    for(int i=0;i<2;i++){
        I l=i?lr:ll;
        Z p2=up(l.hi*l.hi,S),p3=up(p2*l.hi,S);
        if(iw && ab(i?wr:wl)*p2>(iw*S*S-1)/1000)return false;
        if(ir>0 && ab(i?rr:rl)*p3>(ir*S*S-1)/1000)return false;
        if(ir && ab(i?qr:ql)*p3>(ab(ir)*S*(S-z)-1)/1000)return false;
    }
    return true;
}
int main(){
    setvbuf(stdout,nullptr,_IONBF,0);
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
    int prev=2, k=0; a=acc(State{},2);
    std::vector<int> failures(sizeof(ts)/sizeof(ts[0])), last(failures.size());
    for(int p:primes){
        if(p==2)continue;
        if(1000LL*p>=ts[0].x1000){
            I rp=logi(p),rl=logi(prev);
            for(Test t:ts){
                if(t.x1000<1000LL*p && !verify(a,G,M,B,t.x1000<=1000LL*prev?rl:log1000i(t.x1000),rp,t.r,t.w)){
                    failures[k]++;last[k]=p;
                }
                k++;
            }
            k=0;
        }
        a=acc(a,p);prev=p;
    }
    for(Test t:ts){
        if(!verify(a,G,M,B,logi(prev),logi(N),t.r,t.w)){failures[k]++;last[k]=N;}
        printf("%lld %d %d : %d (last %d)\n",(long long)t.x1000,t.r,t.w,failures[k],last[k]); k++;
    }
    printf("prime count at %d: %zu\n",N,primes.size());
    for(int f:failures)require(f==0);
}
