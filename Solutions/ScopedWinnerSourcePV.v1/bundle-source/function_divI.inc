static I divI(I a,I b){if(((b.lo)==0))fail();else ;
I r={(mulU((a.lo),S)/(b.hi)),ceilDiv(mulU((a.hi),S),(b.lo))};
return r;}
