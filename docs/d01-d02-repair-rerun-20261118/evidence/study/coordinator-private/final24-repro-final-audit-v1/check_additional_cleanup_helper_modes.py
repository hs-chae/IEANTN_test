from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,time
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def pin(p):return{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
 helper=R/'reproduction/apply_final24_additional_regenerable_cleanup.py';preview=R/'evidence/FINAL24_ADDITIONAL_METADATA_AND_PLOT_INSTALL_CLEANUP_PREVIEW_V1.json';inputs=[pin(helper),pin(preview),pin(R/'reproduction/apply_final24_regenerable_cleanup.py')];need('assert 'not in helper.read_text()and'__debug__'not in helper.read_text(),'explicit acceptance remains optimization-independent');logs=D/'additional-cleanup-helper-cli-controls-v1';logs.mkdir(exist_ok=False);records=[]
 for mode in [[],['-O'],['-OO']]:
  for action in ['check','reject-unapproved-apply']:
   argv=[sys.executable,'-I','-B',*mode,str(helper),'--preview',str(preview),'--check'if action=='check'else'--apply'];start=time.monotonic();result=subprocess.run(argv,capture_output=True,text=True);label=('normal'if not mode else mode[0][1:])+'-'+action;out=logs/(label+'.stdout');err=logs/(label+'.stderr');out.write_text(result.stdout);err.write_text(result.stderr)
   if action=='check':
    need(result.returncode==0 and not result.stderr,'actual additional cleanup read-only check succeeds');a=json.loads(result.stdout);need(a['targets']==5 and a['regular_files']==29975 and a['payload_bytes']==6606331278 and a['deletion_calls']==0,'all exact target counts and no deletion')
   else:need(result.returncode==1 and'explicit Root additional five-target authority required'in result.stderr,'actual no-authority apply fails before deletion')
   for ref in inputs:need(pin(Path(ref['path']))==ref,'reviewed source/preview changed during actual checks')
   records.append({'label':label,'argv':argv,'returncode':result.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':pin(out),'stderr':pin(err)})
 value={'status':'PASS_SIX_ACTUAL_NORMAL_O_OO_ADDITIONAL_FIVE_TREE_READONLY_CHECKS_AND_UNAPPROVED_APPLY_REJECTIONS','inputs':inputs,'controller':pin(Path(__file__)),'python':sys.version,'records':records,'cleanup_calls':0,'Root_apply_authority_created_or_inferred':False,'original27_helper_or_preview_changed':False,'new_mathematical_numerical_program_or_model_execution':False};receipt=D/'ADDITIONAL_FIVE_TREE_CLEANUP_HELPER_ACTUAL_NORMAL_O_OO_CONTROLS_V1.json';need(not receipt.exists(),'fresh control receipt');fd,tmp=tempfile.mkstemp(prefix='.'+receipt.name+'.',dir=receipt.parent)
 try:
  with os.fdopen(fd,'w')as stream:stream.write(json.dumps(value,indent=2)+'\n');stream.flush();os.fsync(stream.fileno())
  os.link(tmp,receipt)
 finally:os.unlink(tmp)
 print(json.dumps({'receipt':pin(receipt),'helper':pin(helper),'actual_checks':6,'cleanup_calls':0}))
if __name__=='__main__':main()
