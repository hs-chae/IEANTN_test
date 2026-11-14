static I iinv(I a){RI q=toRI(a);
unsigned int valid=((qc((q.lo),qi(0))>0)||(qc((q.hi),qi(0))<0));
if((!valid)){Q wide=qm(smake(decimal("1000000000000000000000000000000"),0),nu(1));
RI r={qn(wide),wide};
return fromRI(r,0);}else ;
Q l=qv(qi(1),(q.hi));
Q h=qv(qi(1),(q.lo));
RI r={qmin(l,h),qmax(l,h)};
return fromRI(r,(a.ok));}
