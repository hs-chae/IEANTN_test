#!/usr/bin/env python3
"""Self-contained exact-rational discovery control, not a theorem or PV.
Run beside the two support .py files and bundled parameter/Table1 JSON files.
Only the compensated-J transfer changes. A failed lower envelope does not
refute Ramanujan's inequality or rule out other mathematical proofs.
"""
import hashlib,inspect,json,sys
from pathlib import Path
import refined_ram_p8_p1_16 as m
B=Path(__file__).resolve().parent
class ScoutFailure(ValueError):
 def __init__(self,data):self.data=data;super().__init__('fixed depth criterion did not certify')
def main():
 parameters=json.loads((B/'MATCHED_TRANSFER_PARAMETERS.json').read_text())
 table=json.loads((B/'MATCHED_TABLE1.json').read_text())
 rows=[tuple(m.Q(x)for x in row)for row in table['rows']]
 m.tables_psi=lambda:rows
 original_req=m.req
 def observed_req(condition,*why):
  if not condition and why and why[0]=='depth cap':
   values=inspect.currentframe().f_back.f_locals
   raise ScoutFailure({k:str(values[k])for k in ['l','u','lower']})
  return original_req(condition,*why)
 m.req=observed_req;m.control();outcomes=[]
 for name,transfer in [('old_GM',lambda l:m.Q('.2772')/l+14*l*m.hi(-l/2)),('new_GM',lambda l:m.Q('.1386')/(l-6)+m.Q('14.44')*l*m.hi(-l/2))]:
  m.eshift=transfer
  try:
   result=m.run(int(parameters['onset']),target=m.Q(parameters['target_margin']),depth_cap=parameters['depth_cap'])
   outcomes.append({'transfer':name,'status':'SCOUT_LOWER_ENCLOSURE_ABOVE_TARGET','visited':result[0],'empty':result[1],'accepted_slabs':result[2],'minimum_lower_enclosure':str(result[3])})
  except ScoutFailure as e:
   outcomes.append({'transfer':name,'status':'SCOUT_DID_NOT_CERTIFY','criterion_failure':e.data,'mathematical_counterexample':False,'resource_failure':False})
 files=['matched_transfer_control.py','refined_ram_p8_p1_16.py','ram_cert.py','MATCHED_TRANSFER_PARAMETERS.json','MATCHED_TABLE1.json']
 result={'schema':'MATCHED_TRANSFER_DISCOVERY_CONTROL_V2','source_first_PV':False,'Lean_theorem':False,'python_version':sys.version,'source_hashes':{x:hashlib.sha256((B/x).read_bytes()).hexdigest()for x in files},'fixed_parameters':parameters,'outcomes':outcomes}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
