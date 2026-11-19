#include <cassert>
#include <iostream>
#include <vector>
#include <algorithm>
using Z=__int128_t;
constexpr Z S=100000000000000000LL;
Z up(Z a,Z b){assert(a>=0 && b>0);return (a+b-1)/b;}
Z mag(Z a){return a<0?-a:a;}
struct I{Z a,b;};
I pt(Z n){return {S*n,S*n};}
I pos(Z n,Z d){return {S*n/d,up(S*n,d)};}
I operator+(I a,I b){return {a.a+b.a,a.b+b.b};}
I operator-(I a,I b){return {a.a-b.b,a.b-b.a};}
I operator*(I a,I b){
 assert(a.a>=0 && b.a>=0);
 assert(!a.b || b.b<(Z(1)<<126)/a.b);
 return {a.a*b.a/S,up(a.b*b.b,S)};
}
I divi(I a,Z d){assert(a.a>=0 && d>0);return {a.a/d,up(a.b,d)};}
I rat(I a,I b){
 assert(a.a>=0 && b.a>0 && a.b<(Z(1)<<126)/S);
 return {a.a*S/b.b,up(a.b*S,b.a)};
}
I logUnit(I x){ // exact argument in [1,2]; enclosing endpoint also in [1,2]
 assert(x.a>=S && x.b<=2*S);
 I z={S*(x.a-S)/(x.a+S),up(S*(x.b-S),x.b+S)};
 I w=z*z,v=z,y=v;
 for(Z k=1;k<22;k++){v=v*w;y=y+divi(v,2*k+1);}
 Z err=3*(v*w).b;
 return {2*y.a,2*y.b+err};
}
const I LOG2=logUnit(pt(2));
I lg(I x) {
 assert(x.a>=S);
 int k=0;while(x.a>=2*S){x=divi(x,2);k++;}
 assert(x.b<=2*S);
 I t=logUnit(x);
 return {t.a+k*LOG2.a,t.b+k*LOG2.b};
}
I lg1(I x){ // x>=1/2; use lg(2x)-log2 if below 1
 if(x.a>=S)return lg(x);
 assert(x.a>=S/2);
 return lg({2*x.a,2*x.b})-LOG2;
}
Z abs2(I l,I r){return std::max({mag(l.a),mag(l.b),mag(r.a),mag(r.b)});}
Z prodhi(Z posi,Z nega){
 I u={posi,posi},v={nega,nega};
 assert(posi<S/2 && nega<S/2);
 I p=u+rat(u*u,pt(2)-divi(pt(2)*u,3));
 I n=v-divi(v*v,2)+divi(v*v*v,6);
 return std::max(p.b,n.b);
}
int main(){
 const int N=67000000;
 std::vector<bool> ok(N+1,true);ok[0]=ok[1]=false;
 for(int k=2;k*k<=N;k++)if(ok[k])for(int j=k*k;j<=N;j+=k)ok[j]=false;
 I h=pt(0);
 const int K=300000;
 for(int i=1;i<=K;i++)h=h+pos(1,i);
 I gn=h-lg(pt(K))-pos(1,2*K);gn.b+=pos(1,Z(K)*K).b;
 I M=gn,B=gn;
 for(int p=2;p<=N;p++)if(ok[p]){
  M=M+lg1(pos(p-1,p))+pos(1,p);
  B=B+divi(lg(pt(p)),Z(p)*(p-1));
 }
 I L=lg(pt(N)), eps=rat(pos(2083,100),L*L*L), U=pt(1)+pt(3)*eps, D=pt(1)-pt(3)*eps;
 I mlo=divi(rat(pt(1),L+pt(1))-rat(pt(3)*eps,L),2*N);
 I mhi=divi(rat(U,L),2*(N-1));
 M={M.a-mhi.b,M.b-mlo.a};
 B={B.a+divi(D,N).a,B.b+divi(U,N-1).b};
 I sl=pt(0),sr=pt(0),sw=pt(0);
 int prev=2;I ll=lg(pt(2)); // use left limit even at right endpoints
 const int cs[8]={100,150,200,250,300,400,600,1000};
 int bad[4][8]={{0}};long count=0;
 const int source[4]={2278382,2278382,2278383,912560};
 bool audit[4]={}; int audit_end[4]={};
 for(int p=2;p<=N;p++)if(ok[p]||p==N){
  I lr=lg(pt(p));
  // At prev after update, and at p from the left.
  I la=lg1(ll),lb=lg1(lr);
  I al=sl+gn+la, ar=sl+gn+lb;
  Z posi=std::max(Z(0),ar.b),nega=std::max(Z(0),-al.a);
  Z ep=prodhi(posi,nega), eq=prodhi(nega,posi);
  Z e=abs2(sr-M-la,sr-M-lb), f=abs2(sw+B-ll,sw+B-lr);
  I r2=lr*lr,r3=r2*lr;
  Z v[4]={(I{ep,ep}*r3).b,(I{eq,eq}*r3).b,(I{e,e}*r3).b,(I{f,f}*r2).b};
  for(int j=0;j<4;j++)for(int k=0;k<8;k++)if(v[j]>pos(cs[k],1000).a)bad[j][k]=p;
  for(int branch=0;branch<4;branch++)if(prev<source[branch] && source[branch]<=p){
   auto measure=[&](I logx)->Z{
    I a=lg1(logx), b=sl+gn+a;
    Z plus=std::max(Z(0),b.b), minus=std::max(Z(0),-b.a);
    Z r=abs2(sr-M-a,sr-M-a),w=abs2(sw+B-logx,sw+B-logx);
    assert(std::max({plus,minus,r,w})<S/10 && logx.a>10*S);
    I l2=logx*logx,l3=l2*logx;
    Z e=branch==0?prodhi(plus,minus):branch==1?prodhi(minus,plus):branch==2?r:w;
    return (I{e,e}*(branch==3?l2:l3)).b;
   };
   audit_end[branch]=p;
   audit[branch]=std::max(measure(lg(pt(source[branch]))),measure(lr))
      <=pos(branch==3?3:2,10).a;
   Z target=pos(branch==3?3:2,10).a;
   constexpr long long unit=1000000;
   long long l=unit*prev,h=unit*p;
   assert(measure(lr)<=target);
   while(h-l>1){
    auto m=l+(h-l)/2;
    if(measure(lg(pos(m,unit)))<=target)h=m;else l=m;
   }
   assert(measure(lg(pos(h,unit)))<=target);
   std::cout<<"source-onset boundary cell "<<branch<<" "<<prev<<" "<<p<<" "<<audit[branch]
            <<" sufficient final cell start "<<h<<"/"<<unit<<"\n";
  }
  if(ok[p]){
    sl=sl+lg1(pos(p-1,p));sr=sr+pos(1,p);sw=sw+divi(lr,p);count++;
  }
  ll=lr;prev=p;
 }
 // Individual value at N (which may be prime).
 I la=lg1(ll), z=sl+gn+la;
 Z posi=std::max(Z(0),z.b),nega=std::max(Z(0),-z.a);
 Z ep=prodhi(posi,nega),eq=prodhi(nega,posi),e=abs2(sr-M-la,sr-M-la),f=abs2(sw+B-ll,sw+B-ll);
 I r2=ll*ll,r3=r2*ll;
 Z v[4]={(I{ep,ep}*r3).b,(I{eq,eq}*r3).b,(I{e,e}*r3).b,(I{f,f}*r2).b};
 for(int j=0;j<4;j++)for(int k=0;k<8;k++)if(v[j]>pos(cs[k],1000).a)bad[j][k]=N+1;
 std::cout<<"primes "<<count<<" scanned through "<<N<<"\n";
 for(int j=0;j<4;j++){for(auto p:bad[j])std::cout<<p<<" ";std::cout<<"\n";}
 assert(count==3951767);
 for(int j=0;j<4;j++){assert(audit[j] && bad[j][j==3?4:2]<=audit_end[j]);}
 const int expect[4][8]={
  {12911611,5001809,2278421,1514831,624917,359837,96043,24317},
  {12911611,5001809,2278421,1514831,624917,359837,96043,24317},
  {12914903,5001809,2278421,1514831,624917,359837,96043,24317},
  {18002111,7105289,3452179,1520747,912581,368359,155921,24571}};
 for(int j=0;j<4;j++)for(int k=0;k<8;k++)assert(bad[j][k]==expect[j][k]);
 std::cout<<std::flush; // adjust only after inspecting actual bounds
}
