static I sqrtMatch(I a){I z=sqrtInterval(a);
if((mulU((z.hi),(z.hi))==mulU((a.hi),S)))((z.hi)=addU((z.hi),1));else ;
return z;}
