"""Additional threshold searches; every printed 'certified' row is a closed ray."""
from gap_d02 import *
if __name__=='__main__':
    import sys
    if sys.argv[1]=='far':
        M=Model(37,75); M.anchor(); verify()
        for k,x,y in [(27,1030,807),(28,1070,838),(29,1110,870),(30,1150,902),
                      (31,1200,936),(32,1240,968),(33,1285,1002),(34,1330,1035),(35,1380,1070),(36,1425,1105)]:
            for b,t in [(Q,x),(J,y)]:
                done=False
                for v in (t,t+20,t+40):
                    try:
                        M.monotail(v,b,k,M.dd[k])
                    except AssertionError:
                        continue
                    print('certified far',str(b),v,k,M.dd[k],flush=True)
                    done=True; break
                if not done: print('not certified far',b,t,k,flush=True)
    else:
        M=Model(14,24); M.anchor(); verify()
        for b,x,k,w in [(J,'49.03',6,85),(J,'49.2',6,86),(J,'50',6,87),
                        (J,'185.25',6,145),(J,'209.8',7,1412),(Q,'36.57',4,'.002'),
                        (Q,'49.5',6,24),(Q,'215.5',6,145)]:
            try: M.check(x,300,b,k,w,2)
            except (AssertionError,ValueError) as e: print('not certified',str(b),x,k,w,str(e),flush=True)

