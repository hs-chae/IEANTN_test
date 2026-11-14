static N decimal(const char* s){N a=nu(0);
unsigned int k=0;
while(((s[k])!=0)){if((((s[k])<'0')||((s[k])>'9')))fail();else ;
(a=na(nm(a,nu(10)),nu(((unsigned int)((s[k])-'0')))));
(k=(k+1));}
return a;}
