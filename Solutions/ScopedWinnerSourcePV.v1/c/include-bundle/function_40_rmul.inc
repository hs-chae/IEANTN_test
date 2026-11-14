static RI rmul(RI a,RI b){Q p=qt((a.lo),(b.lo));
Q q=qt((a.lo),(b.hi));
Q r=qt((a.hi),(b.lo));
Q s=qt((a.hi),(b.hi));
RI out={qmin(qmin(p,q),qmin(r,s)),qmax(qmax(p,q),qmax(r,s))};
return out;}
