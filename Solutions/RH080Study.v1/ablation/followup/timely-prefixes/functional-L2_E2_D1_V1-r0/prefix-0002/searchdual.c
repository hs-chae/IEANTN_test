
// Search-only dense simplex. No proof relies on floating output or termination.
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
static int r,c,*B,*N;
static double **D;
static const double eps=1e-10;
static void pivot(int i,int j){
 double *p=D[i], d=1/p[j]; 
 for(int k=0;k<r+2;k++)if(k!=i) {
   double *a=D[k],v=a[j]*d;
   if(fabs(v)>1e-25)for(int l=0;l<c+2;l++)if(l!=j)a[l]-=p[l]*v;
   a[j]=-v;
 }
 for(int l=0;l<c+2;l++)if(l!=j)p[l]*=d;
 p[j]=d;
 int q=B[i];B[i]=N[j];N[j]=q;
}
static int simplex(int phase){
 int obj=(phase==1?r+1:r);
 for(int iter=0;iter<30000;iter++){
  int j=-1;
  for(int k=0;k<=c;k++){
   if(phase==2&&N[k]==-1)continue;
   if(j<0||D[obj][k]<D[obj][j]-eps||(fabs(D[obj][k]-D[obj][j])<=eps&&N[k]<N[j]))j=k;
  }
  if(D[obj][j]>=-eps)return 1;
  int i=-1;
  for(int k=0;k<r;k++)if(D[k][j]>eps){
   double t=D[k][c+1]/D[k][j];
   if(i<0||t<D[i][c+1]/D[i][j]-eps||(fabs(t-D[i][c+1]/D[i][j])<=eps&&B[k]<B[i]))i=k;
  }
  if(i<0)return 0;
  pivot(i,j);
 }
 return 0;
}
int main(int argc,char **argv){
 if(argc!=6)return 1;
 int m=atoi(argv[1]), n=atoi(argv[2]), G=atoi(argv[3]); double A=atof(argv[4]);
 int f=n-m; c=f+1; r=2*(G+1)+f;
 if(f<1||G<2||A<1)return 2;
 B=calloc(r,sizeof(int));N=calloc(c+1,sizeof(int));
 D=calloc(r+2,sizeof(double*));
 for(int i=0;i<r+2;i++)D[i]=calloc(c+2,sizeof(double));
 double pi=acos(-1.);
 for(int k=0;k<=G;k++){
  double u=m*k/(2.*G);
  double q=k?sin(2*pi*u)/(pi*u):2.;
  for(int j=0;j<f;j++){
   double v=k?(2*sin(pi*u/m)*cos(pi*u/m*(2*(m+j)+1)))/(pi*u):2./m;
   D[2*k][j]= v;D[2*k+1][j]=-v;
   q+=(1-A)*v;
  }
  D[2*k][f]=D[2*k+1][f]=-1;
  D[2*k][c+1]=-q;D[2*k+1][c+1]=q;
 }
 for(int j=0;j<f;j++){int i=2*(G+1)+j;D[i][j]=1;D[i][c+1]=A;}
 for(int i=0;i<r;i++){B[i]=c+i;D[i][c]=-1;}
 for(int j=0;j<c;j++)N[j]=j;
 N[c]=-1;D[r+1][c]=1;D[r][f]=1;
 int i=0;for(int k=1;k<r;k++)if(D[k][c+1]<D[i][c+1])i=k;
 if(D[i][c+1]<-eps){
   pivot(i,c);
   if(!simplex(1)||fabs(D[r+1][c+1])>eps*10)return 3;
   for(i=0;i<r;i++)if(B[i]==-1){
    int j=0;for(int k=1;k<=c;k++)if(fabs(D[i][k])>fabs(D[i][j]))j=k;
    if(fabs(D[i][j])>eps)pivot(i,j);
   }
 }
 if(!simplex(2))return 4;
 double x[c];for(int j=0;j<c;j++)x[j]=0;
 for(i=0;i<r;i++)if(B[i]<c&&B[i]>=0)x[B[i]]=D[i][c+1];
 FILE *out=fopen(argv[5],"w");
 fprintf(out,"{\"m\":%d,\"scale\":1000000000000,\"A\":\"%s\",\"coefficients\":[",m,argv[4]);
 for(int j=0;j<n;j++)
  fprintf(out,"%s%lld", j?",":"",j<m?1000000000000LL:(long long)ceil(1e12*fmax(1-A,fmin(1,1-A+x[j-m]))-1e-4));
 fprintf(out,"]}\n");fclose(out);
 printf("%d %d %d %.8g %.12g\n",m,n,G,A,x[f]);
}
