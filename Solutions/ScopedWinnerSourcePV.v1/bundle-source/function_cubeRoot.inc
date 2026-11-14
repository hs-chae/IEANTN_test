static I cubeRoot(I x){if((((x.lo)>(x.hi))||((x.hi)>(16*S))))fail();else ;
U a=floorCube(mulU((x.lo),mulU(S,S)));
U n=mulU((x.hi),mulU(S,S));
U b=floorCube(n);
if((mulU(mulU(b,b),b)!=n))(b=addU(b,1));else ;
I out={a,b};
return out;}
