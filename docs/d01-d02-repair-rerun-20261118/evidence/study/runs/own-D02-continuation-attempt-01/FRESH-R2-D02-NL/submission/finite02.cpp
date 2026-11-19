#include <vector>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <cassert>
#include <array>
using I=__int128_t;
constexpr I S=I(1)<<61;
constexpr int N=2100000000;
I divup(I a,I b){assert(a>=0&&b>0);return (a+b-1)/b;}
struct B{I l,h;};
B operator+(B a,B b){return{a.l+b.l,a.h+b.h};}
B operator-(B a,B b){return{a.l-b.h,a.h-b.l};}
B operator-(B a){return{-a.h,-a.l};}
B div(B a,I n){assert(n>0&&a.l>=0);return{a.l/n,divup(a.h,n)};}
I mag(B a){return std::max(a.h,-a.l);}
B series(I n,I d,int terms) { // 2*atanh(n/d)
 assert(0<=n&&3*n<=d);
 I r=n*S/d,rh=divup(n*S,d), w=r,wh=rh,lo=0,hi=0;
 for(int k=0;k<terms;++k){
  lo+=w/(2*k+1);hi+=divup(wh,2*k+1);
  w=(w*r/S)*r/S;wh=divup(divup(wh*rh,S)*rh,S);
 }
 // exact remaining series is < 2* first omitted power, before factor 2
 return{2*lo,2*hi+4*wh};
}
B t[256],ln2;
B lograt(I n,I d){
 assert(n>=d&&d>0);int k=0;
 while(n>=2*d){d*=2;++k;}
 I i=(256*(n-d))/d;
 I b=n*256-(256+i)*d, z=n*256+(256+i)*d;
 B r=series(b,z,3);
 return r+t[i]+B{k*ln2.l,k*ln2.h};
}
B inv(I n){return{S/n,divup(S,n)};}
B loglog(B l){
 auto z=lograt(l.l,S);auto w=lograt(l.h,S);return{z.l,w.h};
}
B lqstep(int p){
 int terms=(p==2?22:(p<=13?9:(p<=97?5:(p<=1024?3:2))));
 return series(1,2*I(p)-1,terms);
}
B gamma(){
 int n=1000000; B a{0,0};
 for(int k=1;k<=n;++k)a=a+inv(k);
 // H_n-log(n)-1/(2n) < gamma < H_n-log(n)-1/(2n)+1/n^2
 return a-lograt(n,1)-inv(I(2)*n)+B{0,divup(S,I(n)*n)};
}
struct State{B r{0,0},w{0,0},q{0,0};};
void add(State &st,int p,B lp){
 st.r=st.r+inv(p); st.w=st.w+div(lp,p);st.q=st.q+lqstep(p);
}
uint64_t count=0;
// Closed bounding intervals for each real block: adjoining blocks share endpoints.
constexpr std::array<int,12> ends={40000000,66000000,100000000,200000000,300000000,400000000,500000000,750000000,1000000000,1500000000,2000000000,N};
I mx[ends.size()-1][4]={};
int last[4][17]={};
constexpr int levels[4][17]={
 {650,600,550,500,450,400,350,330,300,280,250,220,210,205,200,198,196},
 {650,600,550,500,450,400,350,330,300,280,250,220,210,205,200,198,196},
 {650,600,550,500,450,400,350,330,300,280,250,220,210,205,200,198,196},
 {650,600,550,500,450,400,350,330,300,280,250,220,210,205,200,198,196}};

I scaled(I m,I l,int power) {
 assert(m>=0 && m<=S/8 && l<22*S);
 for(int j=0;j<power;++j)m=(m/S)*l+divup((m%S)*l,S);
 return m;
}
I expm(I m) {
 if(m<=0)return 0;
 assert(m<S);
 return divup(m*S,S-m);
}
// 1-exp(-m) <= m; and both exponents can be handled sign-specifically.
void two(B a,B b,B c,B d,I L,I* m) {
 m[0]=std::max(m[0],scaled(std::max(mag(a),mag(b)),L,3));
 // c,d below are log Q errors.  |Q'−1| <= max(exp(+upper)−1, −lower)
 // and |P'−1| <= max(exp(−lower)−1, upper).
 I lo=std::min(c.l,d.l),hi=std::max(c.h,d.h);
 m[1]=std::max(m[1],scaled(std::max(expm(-lo),hi),L,3));
 m[2]=std::max(m[2],scaled(std::max(expm(hi),-lo),L,3));
}
// Optional close-to-cutoff diagnostics, using actual right-continuous counts.
void probe(const State &st,B ga,B M,B B3,int l,int r) {
 static unsigned i=0;
 constexpr std::array<int,13> a={912559,912560,912579,912580,912581,912582,
  2278380,2278381,2278382,2278383,2278384,2278419,2278420};
 while(i<a.size() && a[i]<r) {
  int x=a[i++]; assert(l<=x);
  B L=lograt(x,1), dl=loglog(L);
  B y[]={div(L,8),st.r-dl-M,st.q-dl-ga,st.w-L+B3};
  std::cout<<"probe "<<x;
  for(B z:y)std::cout<<" "<<(long long)z.l<<" "<<(long long)z.h;
  std::cout<<"\n";
 }
}
void verify(const State &st,B ga,B M,B B3,int l,int r,B lr){
 static size_t k=0;
 if(r<ends[0])return;
 while(k<ends.size()-1 && ends[k]<=r) {
   int x=std::max(l,ends[k]),y=std::min(r,ends[k+1]);
   if(x<=y){
    B ll=x==r?lr:lograt(x,1);
    B lh=y==r?lr:lograt(y,1);
    B dl=loglog(ll),dh=loglog(lh);
    I vals[4]={};
    B a=st.r-dl-M,b=st.r-dh-M,c=st.q-dl-ga,d=st.q-dh-ga;
    assert(mag(c)<=S/8 && mag(d)<=S/8);  // log-product derivative criterion
    two(a,a,c,c,ll.h,vals);
    two(b,b,d,d,lh.h,vals);
    vals[3]=std::max(scaled(mag(st.w-ll+B3),ll.h,2),scaled(mag(st.w-lh+B3),lh.h,2));
    for(int j=0;j<4;++j) {
     mx[k][j]=std::max(mx[k][j],vals[j]);
     for(int i=0;i<17;++i) if(10000*vals[j]>I(levels[j][i])*S)last[j][i]=y;
    }
   }
   // retain this block for the next step when endpoints are equal: verify
   // both sides of a jump if it coincides with a block boundary.
   if(ends[k+1]>=r)break;
   ++k;
 }
}
int main(){
 ln2=series(1,3,22);
 for(int i=0;i<256;++i)t[i]=series(i,512+i,22);
 // Exact balls, inherited finite_final.txt, independently validated D01 floor.
 B ga{1330968705721142527LL,1330968705724449364LL};
 B M{602971519966457486LL,602971520220900258LL};
 B B3{3072725524686065919LL,3072725524719192057LL};
 std::vector<bool> ok(N+1,true); ok[0]=ok[1]=false;
 for(int p=2;p<=N/p;++p)if(ok[p])for(int k=p*p;k<=N;k+=p)ok[k]=false;
 auto ln=lograt(N,1);
 State st;int l=2; B lp;
 for(int p=2;p<=N;++p)if(ok[p]){
  ++count; lp=lograt(p,1);
  if(p>2){verify(st,ga,M,B3,l,p,lp);}
  add(st,p,lp);l=p;
 }
 verify(st,ga,M,B3,l,N,ln);
 std::cout<<"primes "<<count<<" scale "<<(long long)S<<"\n";
 auto out=[](const char *n,B x){std::cout<<n<<" "<<(long long)x.l<<" "<<(long long)x.h<<"\n";};
 out("gamma",ga);out("M",M);out("B3",B3);
 std::cout<<"blocks: left right, then integer uppers in units 0.0001 for S1 P Q Slog\n";
 for(size_t i=0;i+1<ends.size();++i){
  std::cout<<ends[i]<<" "<<ends[i+1];
  for (I m:mx[i])std::cout<<" "<<(long long)divup(10000*m,S);
  std::cout<<"\n";
 }
 for(int j=0;j<4;++j)for(int i=0;i<17;++i)
  std::cout<<"margin "<<j<<" "<<levels[j][i]<<" last "<<last[j][i]<<"\n";
}
