static I positiveSub(I a,I b){I r={(((a.lo)>(b.hi))?((a.lo)-(b.hi)):0),(((a.hi)>(b.lo))?((a.hi)-(b.lo)):0)};
return r;}
