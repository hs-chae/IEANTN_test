"""Small transport adapter; all isolation remains existing agent-sandbox.py."""
from pathlib import Path
import asyncio,json,resource,base64,collections,time,hashlib,datetime,re
import websockets

C=Path(__file__).resolve().parents[1];V=C.parent;W=V.parent
NATIVE=Path('/ryu/hyunsik/.nvm/versions/node/v20.20.0/lib/node_modules/@openai/codex/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex')
HELPER=W/'ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'

READ_ONLY_FS_METHODS=frozenset({'fs/readFile','fs/readDirectory','fs/getMetadata','fs/watch','fs/watchMissing','fs/unwatch'})
def is_runtime_operation(method):
    return method=='process/start' or (isinstance(method,str) and method.startswith('fs/') and method not in READ_ONLY_FS_METHODS)

class ExistingExecutorAdapter:
    def __init__(self,directory,packet,working_directory='/work',operation_limit=None):
        self.directory=Path(directory);self.packet=Path(packet);self.logs=[];self.processes=[];self.working_directory=working_directory
        self.operation_limit=operation_limit;self.operation_count=0;self.method_counts=collections.Counter();self.budget_exceeded=False;self.waiters={};self.serial=0
        self.address_space_limit=4*1024**3;self.cpu_limit=20;self.file_size_limit=2*1024**2
    async def start(self):
        self.directory.mkdir(parents=True,exist_ok=True);root=self.directory/'root';root.mkdir(exist_ok=True)
        spec=json.loads((V/'evidence/execution-preflight/spec-v2.json').read_text())
        spec.update(root=str(root),cwd=self.working_directory,tmpfsSize='64m',tmpSize='16m',command=['/bin/codex','exec-server','--listen','stdio://'])
        spec['entries']=[x for x in spec['entries'] if x['path'] not in ['/task','/work']]
        spec['entries'] += [{'kind':'ro','path':'/task','source':str(self.packet)}, {'kind':'dir','path':'/work'},
                            {'kind':'dir','path':'/home/worker/.codex'}, {'kind':'ro','path':'/bin/codex','source':str(NATIVE)},
                            {'kind':'ro','path':'/bin/sh','source':'/usr/bin/dash'}, {'kind':'ro','path':'/bin/bash','source':'/usr/bin/bash'}]
        if self.working_directory!='/work':spec['entries'].append({'kind':'dir','path':self.working_directory})
        spec['env'].update(PATH='/bin:/usr/bin',CODEX_HOME='/home/worker/.codex',TOKIO_WORKER_THREADS='2',RAYON_NUM_THREADS='2',MALLOC_ARENA_MAX='2')
        self.spec_path=self.directory/'spec.json';self.spec_path.write_text(json.dumps(spec,indent=2)+'\n')
        self.server=await websockets.serve(self._bridge,'127.0.0.1',0)
        return 'ws://127.0.0.1:'+str(self.server.sockets[0].getsockname()[1])
    async def _bridge(self,ws):
        def limits():
            resource.setrlimit(resource.RLIMIT_AS,(self.address_space_limit,self.address_space_limit))
            resource.setrlimit(resource.RLIMIT_CPU,(self.cpu_limit,self.cpu_limit))
            resource.setrlimit(resource.RLIMIT_FSIZE,(self.file_size_limit,self.file_size_limit))
        p=await asyncio.create_subprocess_exec('unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(HELPER),str(self.spec_path),stdin=asyncio.subprocess.PIPE,stdout=asyncio.subprocess.PIPE,stderr=asyncio.subprocess.PIPE,preexec_fn=limits,limit=4*1024**2)
        self.processes.append(p);self.active_process=p
        self.logs.append({'worker_host_pid':p.pid,'controller_cgroup':Path('/proc/self/cgroup').read_text(),'worker_host_cgroup':Path('/proc/'+str(p.pid)+'/cgroup').read_text()})
        async def inbound():
            async for frame in ws:
                data=frame.encode() if isinstance(frame,str) else frame
                message=json.loads(data);method=message.get('method');self.method_counts[method]+=1
                self.logs.append({'direction':'to_executor','message':message,'monotonic':time.monotonic()})
                if is_runtime_operation(method):
                    self.operation_count+=1
                    if self.operation_limit is not None and self.operation_count>self.operation_limit:
                        self.budget_exceeded=True
                        await ws.send(json.dumps({'id':message.get('id'),'error':{'code':-32000,'message':'Fixed runtime-operation budget exhausted; the attempt is recorded.'}}))
                        continue
                p.stdin.write(data+b'\n');await p.stdin.drain()
        async def outbound():
            while line:=await p.stdout.readline():
                message=json.loads(line)
                if message.get('id') in self.waiters:
                    self.waiters.pop(message['id']).set_result(message)
                    continue
                self.logs.append({'direction':'from_executor','message':message,'monotonic':time.monotonic()})
                await ws.send(line.decode().rstrip('\n'))
        tasks=[asyncio.create_task(inbound()),asyncio.create_task(outbound())]
        try:
            done,pending=await asyncio.wait(tasks,return_when=asyncio.FIRST_COMPLETED)
        finally:
            for t in tasks:t.cancel()
            if p.stdin:p.stdin.close()
            try:await asyncio.wait_for(p.wait(),2)
            except asyncio.TimeoutError:
                p.kill();await p.wait()
            self.logs.append({'worker_exit':p.returncode,'stderr':(await p.stderr.read()).decode(errors='replace')[-4000:]})
    async def snapshot_submission(self,directory):
        directory=Path(directory);directory.mkdir(parents=True,exist_ok=False);(directory/'files').mkdir()
        receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'IN_PROGRESS','unlocked_diagnostic_only':True,'eligible_for_scoring':False,'files':[],'skipped':[],'limits':{'files':17,'total_bytes':8*1024**2,'file_bytes':2*1024**2,'seconds':6},'bytes_are_not_an_atomic_directory_snapshot':True}
        async def capture():
            listed=await self.list_submission();receipt['listing']=listed
            if 'error' in listed:
                receipt['status']='MISSING_SUBMISSION_DIRECTORY' if listed['error'].get('code')==-32004 else 'LISTING_FAILED';return
            entries=listed.get('result',{}).get('entries')
            if not isinstance(entries,list):raise ValueError('invalid listing schema')
            if not entries:receipt['status']='EMPTY_SUBMISSION_DIRECTORY';return
            receipt['status']='SAVED_UNLOCKED_DRAFT_BYTES';used=0
            for index,entry in enumerate(sorted(entries,key=lambda x:x.get('fileName',''))):
                name=entry.get('fileName')
                if index>=17:receipt['skipped'].append({'name':name,'reason':'file_count_ceiling'});continue
                if not isinstance(name,str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',name) or not entry.get('isFile'):
                    receipt['skipped'].append({'name':name,'reason':'nonflat_or_nonfile'});continue
                metadata=await self.export_metadata(name);receipt.setdefault('metadata',{})[name]=metadata
                m=metadata.get('result',{})
                if m.get('isSymlink') or not m.get('isFile') or not isinstance(m.get('size'),int) or m['size']>2*1024**2 or used+m['size']>8*1024**2:
                    receipt['skipped'].append({'name':name,'reason':'metadata_changed_or_size_or_symlink'});continue
                try:data=await self.read_export('/work/submission/'+name)
                except Exception as exc:receipt['skipped'].append({'name':name,'reason':'read_failed','error':str(exc)});continue
                if used+len(data)>8*1024**2:receipt['skipped'].append({'name':name,'reason':'total_byte_ceiling'});continue
                (directory/'files'/name).write_bytes(data);used+=len(data)
                receipt['files'].append({'path':name,'stored_path':'files/'+name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
            if receipt['skipped']:receipt['status']='PARTIAL_UNLOCKED_DRAFT_BYTES'
        try:await asyncio.wait_for(capture(),6)
        except asyncio.TimeoutError:receipt['status']='TIMED_OUT_PARTIAL_SNAPSHOT'
        except Exception as exc:receipt.update(status='SNAPSHOT_FAILED',error=str(exc))
        receipt['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();temp=directory/'SNAPSHOT.tmp';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.replace(directory/'SNAPSHOT.json');return receipt
    async def export_metadata(self,name):
        if '/' in name or name in {'.','..'}:raise ValueError('flat artifact name required')
        p=getattr(self,'active_process',None)
        if p is None or p.returncode is not None:raise RuntimeError('executor unavailable')
        self.serial+=1;key='trusted-export-'+str(self.serial);future=asyncio.get_running_loop().create_future();self.waiters[key]=future
        message={'id':key,'method':'fs/getMetadata','params':{'path':'file:///work/submission/'+name,'sandbox':None}}
        p.stdin.write((json.dumps(message)+'\n').encode());await p.stdin.drain()
        try:response=await asyncio.wait_for(future,3)
        finally:self.waiters.pop(key,None)
        self.logs.append({'trusted_artifact_metadata':response});return response
    async def list_submission(self):
        p=getattr(self,'active_process',None)
        if p is None or p.returncode is not None:raise RuntimeError('executor unavailable')
        self.serial+=1;key='trusted-export-'+str(self.serial)
        future=asyncio.get_running_loop().create_future();self.waiters[key]=future
        message={'id':key,'method':'fs/readDirectory','params':{'path':'file:///work/submission'}}
        p.stdin.write((json.dumps(message)+'\n').encode());await p.stdin.drain()
        try:response=await asyncio.wait_for(future,3)
        finally:self.waiters.pop(key,None)
        self.logs.append({'trusted_submission_listing':response});return response
    async def read_export(self,path):
        # Trusted read-only post-turn export. Never returned to the model.
        if not path.startswith('/work/submission/') or '..' in Path(path).parts:
            raise ValueError('export outside submission')
        p=getattr(self,'active_process',None)
        if p is None or p.returncode is not None:raise RuntimeError('executor unavailable')
        self.serial+=1;key='trusted-export-'+str(self.serial)
        future=asyncio.get_running_loop().create_future();self.waiters[key]=future
        message={'id':key,'method':'fs/readFile','params':{'path':'file://'+path,'sandbox':None}}
        p.stdin.write((json.dumps(message)+'\n').encode());await p.stdin.drain()
        try:response=await asyncio.wait_for(future,3)
        finally:self.waiters.pop(key,None)
        self.logs.append({'trusted_export':path,'response':response})
        if 'error' in response:raise RuntimeError(str(response['error']))
        result=response.get('result',{});encoded=result.get('dataBase64')
        if not isinstance(encoded,str):raise ValueError('unexpected readFile response fields '+str(list(result)))
        data=base64.b64decode(encoded,validate=True)
        if len(data)>2*1024**2:raise ValueError('oversized export')
        return data
    async def close(self):
        self.server.close()
        try:await asyncio.wait_for(self.server.wait_closed(),5)
        except asyncio.TimeoutError:
            for p in self.processes:
                if p.returncode is None:p.kill()
            await self.server.wait_closed()
        (self.directory/'transport.json').write_text(json.dumps(self.logs,indent=2)+'\n')
