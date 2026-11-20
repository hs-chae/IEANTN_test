"""Strict numerical-run manifest identities. Ordinary validation, not PV."""
import hashlib,json,math,os,pathlib

def _pairs(xs):
 d={}
 for k,v in xs:
  if k in d:raise ValueError('duplicate JSON key '+k)
  d[k]=v
 return d

def _float(s):
 v=float(s)
 if not math.isfinite(v):raise ValueError('nonfinite float')
 return v

def load(path):
 return json.loads(pathlib.Path(path).read_bytes(),object_pairs_hook=_pairs,parse_float=_float,parse_constant=lambda x:(_ for _ in ()).throw(ValueError('nonfinite '+x)))

def atomic_json(path,obj):
 path=pathlib.Path(path);temp=path.with_name(path.name+'.tmp-'+str(os.getpid()));temp.write_text(json.dumps(obj,indent=2,allow_nan=False)+'\n');temp.replace(path)

def integer(v,label,lo=0,hi=(1<<64)-1):
 if type(v)is not int or not lo<=v<=hi:raise ValueError('integer domain '+label)
 return v

def validate(run,scratch,solution):
 if run['status']!='UNTRUSTED_NUMERICAL_GENERATION_COMPLETE' or run['formal_verification']is not False:raise ValueError('generator status')
 mode=run['mode']
 if mode not in ['actual','unit']:raise ValueError('mode')
 begin=integer(run['begin'],'begin',38358837683,38358837683);end=integer(run['end_inclusive'],'end',begin,1620000000000)+1;chunks=integer(run['chunks'],'chunks',1,256);integer(run['workers'],'workers',1,16)
 records=run['records']
 if type(records)is not list or len(records)!=chunks:raise ValueError('complete chunk universe')
 if run['source_sha256']!=hashlib.sha256((solution/'c/generate_finite.cpp').read_bytes()).hexdigest():raise ValueError('generator source identity')
 if run['executable_sha256']!=hashlib.sha256((scratch/'generate_finite').read_bytes()).hexdigest():raise ValueError('generator executable identity')
 total=0
 for i,rec in enumerate(records):
  b=begin+(end-begin)*i//chunks;e=begin+(end-begin)*(i+1)//chunks
  if type(rec)is not dict or rec['chunk']!=i or type(rec['chunk'])is not int or rec['begin']!=b or rec['end_exclusive']!=e or rec['exit_code']!=0:raise ValueError('exact chunk partition')
  nr=rec['numeric_result']
  if nr['status']!='UNTRUSTED_NUMERICAL_FINITE_COVERAGE' or nr['mode']!=mode or nr['begin']!=b or nr['end_exclusive']!=e:raise ValueError('child target identity')
  cells=integer(nr['cells'],'cells',1)
  if rec['certificate_bytes']!=cells*56 or nr['certificate_bytes']!=cells*56:raise ValueError('certificate length')
  h=rec['certificate_sha256']
  if type(h)is not str or len(h)!=64 or any(c not in '0123456789abcdef' for c in h):raise ValueError('sha256')
  total+=cells*56
 if run['certificate_bytes']!=total:raise ValueError('global certificate length')
 return records
