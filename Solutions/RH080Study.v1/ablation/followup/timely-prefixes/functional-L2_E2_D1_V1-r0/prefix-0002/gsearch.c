
// Floating-point search only; gaussian.py is the independent exact checker.
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
static double p(double v){return v>0?v:0;}
static void basis(double *v,int n, double x){
 double u=sqrt(2*acos(-1.))*x, a=exp(-u*u/2),b=sqrt(2.)*u*a;
 v[0]=a;
 for(int j=2;j<2*n;j++){
   double c=sqrt(2./j)*u*b-sqrt((j-1.)/j)*a;
   a=b;b=c;
   if(!(j%2))v[j/2]=c;
 }
}
static double dot(int n,const double *x,const double *y){
 double s=0;for(int j=0;j<n;j++)s+=x[j]*y[j];return s;
}
static void solve(int n,double R[n][n], const double *b,double *u){
 for(int j=0;j<n;j++)u[j]=(b[j]-dot(j,R[j],u))/R[j][j];
 for(int j=n-1;j>=0;j--){
   double w=u[j];for(int k=j+1;k<n;k++)w-=R[k][j]*u[k];u[j]=w/R[j][j];
 }
}
int main(int argc,char **argv){
 if(argc!=9){fprintf(stderr,"n grid(1/step) iters A target rho-f rho-g out\n");return 1;}
 int n=atoi(argv[1]), grid=atoi(argv[2]), iters=atoi(argv[3]), K=(int)ceil(sqrt(2*n/acos(-1.))+3)*grid+1;
 double A=atof(argv[4]),target=atof(argv[5]),rf=atof(argv[6]),rg=atof(argv[7]);
 double (*F)[n]=calloc(K,sizeof(*F));double fx[K],fy[K],wx[K],wy[K],wF[K],wG[K];
 double H[n][n], R[n][n], c[n], base[n], a[n], b[n], jscale[n];
 for(int i=0;i<K;i++){
  basis(F[i],n,(double)i/grid);
  fx[i]=fy[i]=wx[i]=wy[i]=0;
  wF[i]=(i==0||i==K-1?.5:1.)*2/grid;
  wG[i]=(i==grid||i==K-1?.5:1.)*2/grid;
 }
 basis(c,n,0);
 for(int j=0;j<n;j++)for(int k=0;k<n;k++){
  double sf=0,sg=0;
  for(int i=0;i<K;i++){
   double h=F[i][j]*F[i][k];sf+=wF[i]*h;
   if(i>=grid)sg+=wG[i]*h;
  }
  H[j][k]=rf*sf+rg*(1-2*((j+k)%2))*sg;
 }
 for(int j=0;j<n;j++)for(int k=0;k<=j;k++){
  double u=H[j][k]-dot(k,R[j],R[k]);
  R[j][k]=j==k?sqrt(u):u/R[k][k];
 }
 solve(n,R,c,base);
 double den=dot(n,c,base);
 if(!(den>0))return 2;
 for(int it=1;it<=iters;it++){
  for(int j=0;j<n;j++)b[j]=0;
  for(int i=0;i<K;i++){
   double v=rf*wF[i]*(fx[i]-fy[i]),w=i>=grid?rg*wG[i]*(wx[i]-wy[i]):0;
   for(int j=0;j<n;j++)b[j]+=F[i][j]*(v+(1-2*(j%2))*w);
  }
  solve(n,R,b,a);
  double adj=(1-dot(n,c,a))/den;
  for(int j=0;j<n;j++)a[j]+=adj*base[j];
  double M=0,L=0;
  for(int i=0;i<K;i++){
   double f=0,g=0;for(int j=0;j<n;j+=2){f+=F[i][j]*a[j];if(j+1<n)g+=F[i][j+1]*a[j+1];}
   double v=1.75*(f+g)-.75*fx[i]+fy[i];fx[i]=p(v-1/rf)-p(-v-1/rf);fy[i]=v-fx[i];
   M+=wF[i]*fabs(f+g);
   if(i>=grid){v=1.75*(f-g)-.75*wx[i]+wy[i];wx[i]=v>=0?p(v-target*A/rg):v;wy[i]=v-wx[i];L+=wG[i]*p(f-g);}
  }
  if(it%5000==0||it==iters){
   printf("%d %.12f L=%.10f norm=%.10f\n",it,M/(1-A*L),L,M);fflush(stdout);
   FILE*f=fopen(argv[8],"w");
   fprintf(f,"[");for(int j=0;j<n;j++){
      long double s=(long double)a[j]/(ldexpl(1.L,j)*sqrtl(tgammal(2*j+1)));
      // JSON strings in fixed scientific notation are parsed as exact rationals.
      fprintf(f,"%s\"%.22Le\"",j?",":"",s);
   }
   fprintf(f,"]\n");fclose(f);
  }
 }
}
