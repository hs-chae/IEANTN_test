#!/usr/bin/env python3
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib,json,os,subprocess,sys,tempfile
D=Path(__file__).resolve().parent
RUN=D/'browser-final-v3'
if RUN.exists():raise ValueError('fresh output required')
RUN.mkdir();checker=D/'check_reports_browser.py';inputs=D/'BROWSER_INPUTS.json'
base=json.loads(inputs.read_text());wrong=json.loads(inputs.read_text());wrong['reports'][0]['sha256']='0'*64
(RUN/'wrong-sha.json').write_text(json.dumps(wrong))
(RUN/'duplicate.json').write_text('{"reports":[],"reports":[],"support":[]}')
modes=[('normal',[]),('O',['-O']),('OO',['-OO'])]
def run_mode(mode):
 name,flags=mode;prefix=[sys.executable]+flags+[str(checker)]
 commands=[('positive',prefix+['--inputs',str(inputs),'--out',str(RUN/name)],True),('unknown-option',prefix+['--inputs',str(inputs),'--out',str(RUN/(name+'-unknown')),'--unknown'],False),('missing-input',prefix+['--out',str(RUN/(name+'-missing'))],False),('wrong-sha',prefix+['--inputs',str(RUN/'wrong-sha.json'),'--out',str(RUN/(name+'-wrong'))],False),('duplicate-key',prefix+['--inputs',str(RUN/'duplicate.json'),'--out',str(RUN/(name+'-duplicate'))],False)]
 records=[]
 for label,cmd,positive in commands:
  r=subprocess.run(cmd,capture_output=True,text=True)
  (RUN/(name+'-'+label+'.stdout')).write_text(r.stdout);(RUN/(name+'-'+label+'.stderr')).write_text(r.stderr)
  if (r.returncode==0)!=positive:raise ValueError((name,label,r.returncode,r.stderr))
  if not positive and any((RUN/(name+'-'+suffix)/'RESULT.json').exists()for suffix in ['unknown','missing','wrong','duplicate']):raise ValueError('negative wrote result')
  records.append({'case':label,'command':cmd,'returncode':r.returncode})
 result=json.loads((RUN/name/'RESULT.json').read_text())
 if result['python_optimization']!=len(flags) and name=='normal':raise ValueError('wrong optimization mode')
 expected={'normal':0,'O':1,'OO':2}[name]
 if result['python_optimization']!=expected:raise ValueError('optimization mode mismatch')
 return {'mode':name,'cases':records,'browser_result_sha256':hashlib.sha256((RUN/name/'RESULT.json').read_bytes()).hexdigest(),'optimization':expected}
with ThreadPoolExecutor(max_workers=3)as pool:records=list(pool.map(run_mode,modes))
result={'status':'PASS_ACTUAL_BROWSER_CLIS_NORMAL_O_OO_3_POSITIVE_12_NEGATIVE','checker_sha256':hashlib.sha256(checker.read_bytes()).hexdigest(),'inputs_sha256':hashlib.sha256(inputs.read_bytes()).hexdigest(),'records':records,'official_Comparator_receipt':False}
fd,tmp=tempfile.mkstemp(prefix='.RESULT-',dir=RUN);os.close(fd);Path(tmp).write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,RUN/'RESULT.json');print(result['status'])
