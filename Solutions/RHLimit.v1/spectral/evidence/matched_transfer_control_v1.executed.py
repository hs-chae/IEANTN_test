#!/usr/bin/env python3
"""Matched exact-rational discovery control, not a theorem or PV certificate.

Keep Table1, five small-root corrections, upper powers, all21 source coefficients,
slab subdivision,620b onset, target.001, and global1.6 fixed. Change only the
already proved old/new compensated-J transfer. Failure means this fixed lower-
envelope algorithm did not certify, never that Ramanujan's inequality fails.
"""
import json,hashlib
from pathlib import Path
import refined_ram_p8_p1_16 as m

def main():
 m.control();rows=[]
 for name,transfer in [('old_GM',lambda l:m.Q('.2772')/l+14*l*m.hi(-l/2)),('new_GM',lambda l:m.Q('.1386')/(l-6)+m.Q('14.44')*l*m.hi(-l/2))]:
  m.eshift=transfer
  try:
   result=m.run(620000000000,target=m.Q('.001'),depth_cap=30)
   rows.append({'transfer':name,'status':'SCOUT_CERTIFIED_LOWER_ENVELOPE','visited':result[0],'empty':result[1],'accepted_slabs':result[2],'minimum_lower_enclosure':str(result[3])})
  except ValueError as e:
   rows.append({'transfer':name,'status':'SCOUT_DID_NOT_CERTIFY','diagnostic':str(e),'mathematical_counterexample':False,'resource_failure':False})
 result={'schema':'MATCHED_TRANSFER_DISCOVERY_CONTROL_V1','source_first_PV':False,'Lean_theorem':False,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'fixed_inputs':'Same Table1 data,sourcepolynomial,primepower bounds,global1.6,620b,.001,slabalgorithm; onlytransferchanged','outcomes':rows}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
