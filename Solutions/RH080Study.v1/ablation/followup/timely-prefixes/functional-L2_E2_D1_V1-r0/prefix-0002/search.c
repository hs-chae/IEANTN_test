
// Search only. Rounded candidates require an independent continuum certificate.
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <complex.h>
static int K,*rev; static double complex *roots;
static double complex *z;
static void fft(int inverse) {
  for(int i=1;i<K;i++) if(rev[i]<i) {double complex c=z[i];z[i]=z[rev[i]];z[rev[i]]=c;}
  for(int w=2;w<=K;w*=2) for(int i=0;i<K;i+=w) for(int j=0;j<w/2;j++){
    double complex r=roots[j*(K/w)]; if(inverse)r=conj(r);
    double complex q=z[i+j+w/2]*r, v=z[i+j];z[i+j]=v+q;z[i+j+w/2]=v-q;
  }
}
static double plus(double v){return v>0?v:0;}
static double soft(double v,double t){return plus(v-t)-plus(-v-t);}
static double posarea(double a,double b) {
 if(a>=0&&b>=0)return (a+b)/2;if(a<=0&&b<=0)return 0;
 double c=fmax(a,b);return c*c/(2*fabs(a-b));
}
int main(int argc,char**argv){
 if(argc!=10){fprintf(stderr,"m n K iters A target rho-f rho-w out\n");return 1;}
 int m=atoi(argv[1]), n=atoi(argv[2]);K=atoi(argv[3]);int iters=atoi(argv[4]);
 double A=atof(argv[5]), target=atof(argv[6]), rf=atof(argv[7]), rw=atof(argv[8]);
 const int R=8;int E=(n-m)*R+1;
 if(m<1||n<=m||K<2*n||(K&(K-1))||rf<=0||rw<=0)return 2;
 rev=calloc(K,sizeof(int));roots=calloc(K/2,sizeof(*roots));z=calloc(K,sizeof(*z));
 for(int i=1;i<K;i++)rev[i]=(rev[i/2]/2)+(i%2)*(K/2);
 for(int i=0;i<K/2;i++)roots[i]=cexp(-2*acos(-1.)*I*i/K);
 double fx[K],fy[K],wx[E],wy[E],lo[n],dd[n],d[n],e[n],base[n],x[n+1],rhs[n];
 for(int i=0;i<K;i++)fx[i]=fy[i]=0;
 for(int i=0;i<E;i++)wx[i]=wy[i]=0;
 for(int j=0;j<n;j++){d[j]=rf*(j?2:1);e[j]=lo[j]=0;}
 for(int k=0;k<E;k++){
   int j=m+k/R;if(j==n)break;double t=(double)(k%R)/R;
   d[j]+=rw*(1-t)*(1-t);
   if(j+1<n){d[j+1]+=rw*t*t;e[j+1]+=rw*t*(1-t);}
 }
 dd[0]=d[0];for(int j=1;j<n;j++){lo[j]=e[j]/dd[j-1];dd[j]=d[j]-lo[j]*e[j];}
 for(int j=0;j<n;j++)base[j]=(j?2:1)-(j?lo[j]*base[j-1]:0);
 for(int j=n-1;j>=0;j--)base[j]=(base[j]-(j+1<n?e[j+1]*base[j+1]:0))/dd[j];
 double eq=0;for(int j=0;j<n;j++)eq+=(j?2:1)*base[j];
 for(int it=1;it<=iters;it++){
   for(int i=0;i<K;i++)z[i]=fx[i]-fy[i];
   fft(1);
   for(int j=0;j<n;j++)rhs[j]=(j?2:1)*creal(z[j])*(rf/K);
   for(int k=0;k<E;k++){
     int j=m+k/R;if(j==n)break;double t=(double)(k%R)/R,v=rw*(wx[k]-wy[k]);
     rhs[j]+=(1-t)*v;if(j+1<n)rhs[j+1]+=t*v;
   }
   for(int j=1;j<n;j++)rhs[j]-=lo[j]*rhs[j-1];
   x[n]=0;double val=0;
   for(int j=n-1;j>=0;j--){x[j]=(rhs[j]-(j+1<n?e[j+1]*x[j+1]:0))/dd[j];val+=(j?2:1)*x[j];}
   for(int j=0;j<n;j++)x[j]+=base[j]*(m-val)/eq;
   for(int i=0;i<K;i++)z[i]=0;z[0]=x[0];
   for(int j=1;j<n;j++)z[j]=z[K-j]=x[j];
   fft(0);
   for(int i=0;i<K;i++){double v=1.7*creal(z[i])-.7*fx[i]+fy[i];fx[i]=soft(v,1/rf);fy[i]=v-fx[i];}
   for(int k=0;k<E;k++){
     int j=m+k/R;double t=(double)(k%R)/R,r=j<n?(1-t)*x[j]+t*x[j+1]:0;
     double v=1.7*r-.7*wx[k]+wy[k],c=target*A*2/(m*R*rw)*(k==0?.5:1);
     wx[k]=v>0?plus(v-c):v;wy[k]=v-wx[k];
   }
   if(it%2000==0||it==iters){
    double norm=0,L=0;for(int i=0;i<K;i++)norm+=fabs(creal(z[i]))/K;
    for(int j=m;j<n;j++)L+=2*posarea(x[j],x[j+1])/m;
    fprintf(stderr,"%d %.12f L=%.9f gridNorm=%.9f\n",it,norm/(1-A*L),L,norm);
    FILE*f=fopen(argv[9],"w");
    fprintf(f,"{\n\"m\":%d,\"scale\":1000000000000,\"A\":\"%.15g\",\"coefficients\":[\n",m,A);
    for(int j=0;j<n;j++)fprintf(f,"%s%lld",j?",":"",(long long)llround(x[j]*1e12));
    fprintf(f,"]}\n");fclose(f);
   }
 }
}
