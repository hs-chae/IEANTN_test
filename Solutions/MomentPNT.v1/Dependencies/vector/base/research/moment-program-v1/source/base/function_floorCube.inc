static U floorCube(U n){U lo=0;
U hi=(4*S);
while((lo<hi)){U m=((lo+((hi-lo)/2))+1);
if((mulU(mulU(m,m),m)<=n))(lo=m);else (hi=(m-1));}
return lo;}
