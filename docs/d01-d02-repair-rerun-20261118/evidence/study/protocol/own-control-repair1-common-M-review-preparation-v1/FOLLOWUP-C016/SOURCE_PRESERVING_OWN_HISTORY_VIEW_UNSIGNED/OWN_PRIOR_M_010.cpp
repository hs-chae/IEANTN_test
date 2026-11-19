#define main candidate_main
#include "/work/exact/mertens.cpp"
#undef main

// Diagnostic: this is the SAME sufficient test for form 1, with the
// locked M interval. No new parameter search or more precise M.
int main(){
  ln2=core(2,1);
  const long long targets[]={2278382186LL,5001781860LL,8789120961LL};
  const int coef[]={200,150,120};
  int n=targets[2]/1000;
  std::vector<bool> c(n+1);
  for(int p=2;p*p<=n;++p)if(!c[p])for(int j=p*p;j<=n;j+=p)c[j]=true;
  Z s=0,k=0;
  int j=2;
  for(int i=0;i<3;++i){
    long long x=targets[i];
    for(;j<=x/1000;++j)if(!c[j])s+=F/j,++k;
    Z L=logscaled(x,1000),ll=logscaled(L,F);
    Bound d{s-Z(1205943040550885117LL)-ll-(LE+1),
            s+k-Z(1205943018564608864LL)-ll};
    Z b=F*coef[i]/1000;
    for(int h=0;h<3;++h)b=b*F/(L+LE);
    printf("x*1000=%lld ",x);
    pairout("form-1 interval",d);
    pairout("padded test: budget absUpper",Bound{b,absup(d)});
    assert(absup(d)>b);
  }
}
