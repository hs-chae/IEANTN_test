static I subExact(I a,I b){if((((a.lo)<(b.hi))||((a.hi)<(b.lo))))fail();else ;
I z={((a.lo)-(b.hi)),((a.hi)-(b.lo))};
return z;}
