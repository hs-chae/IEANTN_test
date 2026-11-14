static I fromRI(RI a,unsigned int ok){Q factor={smake(scale100,0),nu(1)};
I out={floorQ(qt((a.lo),factor)),ceilQ(qt((a.hi),factor)),ok};
return out;}
