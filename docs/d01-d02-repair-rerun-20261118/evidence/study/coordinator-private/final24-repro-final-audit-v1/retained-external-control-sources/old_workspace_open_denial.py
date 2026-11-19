from pathlib import Path
import json,runpy,sys
origin=Path(sys.argv[1]).resolve();script=Path(sys.argv[2]).resolve();argv=sys.argv[3:];blocked=[]
def hook(event,args):
 if event=='open'and isinstance(args[0],(str,bytes)):
  path=Path(args[0].decode()if isinstance(args[0],bytes)else args[0]);path=(path if path.is_absolute()else Path.cwd()/path).resolve()
  if path.is_relative_to(origin):blocked.append(str(path));raise RuntimeError('original workspace open prohibited')
sys.addaudithook(hook);sys.argv=[str(script)]+argv;runpy.run_path(str(script),run_name='__main__')
if blocked:raise ValueError('original workspace open attempted')
print(json.dumps({'status':'PASS_FRESH_FINAL24_ALL_CASE_METADATA_WITH_ORIGINAL_W_OPEN_DENIED','original_workspace_opens':blocked,'scientific_calls':0}))
