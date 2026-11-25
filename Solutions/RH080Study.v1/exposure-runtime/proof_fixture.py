"""Synthetic NOAUTH provider requesting actual Lean imports inside its worker.

The model server is a deterministic local HTTP handler. This changes only the
neutral fixture's requested diagnostic program, never executor permissions.
"""
import json
import time


def worker_script(mode):
    return r'''import os,json,hashlib,subprocess,re
mode=MODE
os.makedirs('/work/submission',exist_ok=True)
canary=b'NEUTRAL_FIXTURE_NOT_A_MATHEMATICAL_CANDIDATE\n'
open('/work/submission/canary.txt','wb').write(canary)
probe={'task_bytes':len(open('/task/TASK.md','rb').read()),'host_absent':not os.path.exists('/ryu/hyunsik/playground/independence/codex/ivy/memory'),'controller_canary_absent':not os.path.exists('host-only-canary.txt'),'auth_absent':not os.path.exists('/home/worker/.codex/auth.json'),'pid_namespace':os.readlink('/proc/self/ns/pid'),'net_namespace':os.readlink('/proc/self/ns/net'),'genericLean_available':os.path.isfile('/opt/lean/bin/lean'),'cache_probe':'neutral'}
print(json.dumps(probe),flush=True)
allowed={'propext','Classical.choice','Quot.sound'}
statements={'D':'import CompactDualVerified\n#check RH080.Dual.compact_grid_from_integer_caps\n#check RH080.Dual.kernel_compact_global\n#print axioms RH080.Dual.compact_grid_from_integer_caps\n#print axioms RH080.Dual.kernel_compact_global\n','C':'import CompactDualSourceFirst\n#check RH080.Dual.actual_source_first_functional_result\n#print axioms RH080.Dual.actual_source_first_functional_result\n'}
rows=[]
for name,source in statements.items():
 path='/work/'+name+'Probe.lean';open(path,'w').write(source)
 command=['/bin/lean','--root=/work',path]
 result=subprocess.run(command,capture_output=True,text=True,timeout=150)
 axioms=[set(v.strip() for v in text.split(',') if v.strip()) for text in re.findall(r"depends on axioms: \[([^]]*)\]",result.stdout)]
 if name=='D':passed=result.returncode==0 and len(axioms)==2 and all(x<=allowed for x in axioms)
 elif mode=='V1':passed=result.returncode==0 and len(axioms)==1 and all(x<=allowed for x in axioms)
 else:passed=result.returncode!=0 and not os.path.exists('/source_pv/objects/CompactDualSourceFirst.olean') and ('unknown module' in result.stdout or 'does not exist' in result.stdout or 'not found' in result.stdout)
 rows.append({'kind':name,'command':command,'returncode':result.returncode,'stdout':result.stdout,'stderr':result.stderr,'accepted':passed,'axioms':[sorted(x) for x in axioms]})
 open('/work/submission/'+name+'Probe.lean','w').write(source)
value={'status':'PASS_ACTUAL_ASSIGNED_PROOF_IMPORT_MANIPULATION' if all(x['accepted'] for x in rows) else 'FAILED_ACTUAL_ASSIGNED_PROOF_IMPORT_MANIPULATION','mode':mode,'checks':rows,'actual_lean_path':os.environ.get('LEAN_PATH'),'actual_bin_lean_wrapper':open('/bin/lean').read(),'lean_version':subprocess.check_output(['/bin/lean','--version'],text=True).strip(),'source_C_object_present':os.path.isfile('/source_pv/objects/CompactDualSourceFirst.olean'),'no_native_axiom_in_successful_audits':all(all(x<=allowed for x in [set(a) for a in r['axioms']]) for r in rows if r['returncode']==0)}
raw=(json.dumps(value,indent=2)+'\n').encode();open('/work/submission/PROOF_IMPORTS.json','wb').write(raw)
files=[]
for name in ['canary.txt','DProbe.lean','CProbe.lean','PROOF_IMPORTS.json']:
 data=open('/work/submission/'+name,'rb').read();files.append({'path':name,'sha256':hashlib.sha256(data).hexdigest()})
open('/work/submission/LOCK.json','w').write(json.dumps({'files':files}))
print(json.dumps({'proof_import_status':value['status'],'mode':mode}),flush=True)
'''.replace('MODE',repr(mode),1)


def handler(base,mode):
    class ProofImports(base):
        def do_POST(self):
            import shlex
            data=json.loads(self.rfile.read(int(self.headers['Content-Length'])));self.server.requests.append(data)
            n=len(self.server.requests)
            if n==1:
                script=worker_script(mode)
                arguments={'cmd':'/usr/bin/python3.10 -I -c '+shlex.quote(script),'shell':'/bin/bash','login':False,'yield_time_ms':30000,'max_output_tokens':1500}
                offered={tool.get('name'):tool.get('type')for tool in data.get('tools',[])}
                if offered.get('exec_command')=='function':
                    item={'id':'proof-import-call','type':'function_call','call_id':'proof-import-call','name':'exec_command','arguments':json.dumps(arguments)}
                else:
                    item={'id':'proof-import-call','type':'custom_tool_call','call_id':'proof-import-call','name':'exec','namespace':'functions','input':'text(await tools.exec_command('+json.dumps(arguments)+'));'}
            else:
                item={'id':'final','type':'message','role':'assistant','status':'completed','content':[{'type':'output_text','text':'NEUTRAL_PROOF_IMPORT_FIXTURE_COMPLETE','annotations':[]}]}
            usage={'input_tokens':7,'output_tokens':3,'total_tokens':10,'output_tokens_details':{'reasoning_tokens':1}}
            response={'id':'fixture'+str(n),'object':'response','created_at':int(time.time()),'model':data['model'],'status':'completed','output':[item],'usage':usage}
            events=[{'type':'response.created','response':{**response,'status':'in_progress','output':[]}},{'type':'response.output_item.added','output_index':0,'item':item},{'type':'response.output_item.done','output_index':0,'item':item},{'type':'response.completed','response':response}]
            payload=''.join('event: '+event['type']+'\ndata: '+json.dumps(event)+'\n\n'for event in events).encode()
            self.send_response(200);self.send_header('Content-Type','text/event-stream');self.send_header('Content-Length',str(len(payload)));self.end_headers();self.wfile.write(payload)
    return ProofImports
