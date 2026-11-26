#!/usr/bin/env python3
"""Run one owned proof command with independent RAM/disk reserve checks.

The caller establishes the owned cgroup. A scan that loses a concurrently
renamed file is retried; an incomplete scan never establishes admission.
This supervisor records execution resources, not mathematical acceptance.
"""
import argparse,hashlib,json,os,signal,subprocess,time
from pathlib import Path

GiB=2**30
def need(ok,message):
    if not ok:raise RuntimeError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def publish(path,value):
    need(not path.exists(),'Fresh receipt required')
    path.parent.mkdir(parents=True,exist_ok=True)
    temp=path.with_name(path.name+'.pending')
    with temp.open('x')as stream:
        json.dump(value,stream,indent=2,allow_nan=False);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    try:os.link(temp,path)
    finally:temp.unlink()
def available():
    return int(next(line.split()[1]for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:')))*1024
def disk_scan(root,runner=subprocess.run):
    failures=[]
    for attempt in range(5):
        r=runner(['du','-sB1','--',str(root)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if r.returncode==0:
            fields=r.stdout.split();need(len(fields)>=2 and fields[0].isdigit(),'Malformed complete disk scan')
            return int(fields[0]),failures
        failures.append(dict(attempt=attempt+1,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr))
    raise RuntimeError('No complete disk scan after five attempts: '+json.dumps(failures))
def cgroup():
    relative=next(line.split(':',2)[2]for line in Path('/proc/self/cgroup').read_text().splitlines()if line.startswith('0::'))
    need(relative not in ['','/'],'Owned cgroup required')
    path=Path('/sys/fs/cgroup')/relative.lstrip('/')
    return dict(path=str(path),**{name:(path/name).read_text().strip()for name in ['memory.current','memory.max','memory.high','memory.swap.max','memory.events','cpu.stat']if(path/name).is_file()})
def terminate_group(pid,which):
    try:os.killpg(pid,which)
    except ProcessLookupError:pass
def interrupted(which,frame):
    raise InterruptedError('Supervisor received signal '+str(which))
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['root','command','receipt','live']:ap.add_argument('--'+name,required=True,type=Path)
    a=ap.parse_args();need(not a.receipt.exists(),'Fresh supervisor outcome required')
    plan=json.loads(a.command.read_text());cmd=plan['command']
    need(type(cmd)is list and cmd and all(type(v)is str and v for v in cmd),'Concrete argument vector required')
    for row in plan['source_pins']:need(sha(Path(row['path']))==row['sha256'],'Pinned execution source changed')
    start=time.monotonic();child=None;samples=[];code=None;failure=None;before=None;final=None
    stdout=a.receipt.with_suffix('.stdout');stderr=a.receipt.with_suffix('.stderr')
    for which in [signal.SIGTERM,signal.SIGINT]:signal.signal(which,interrupted)
    try:
        before=cgroup();need(before.get('memory.max')==str(300*GiB)and before.get('memory.swap.max')=='0','Physical300GiB/no-swap owned cgroup required')
        usage,retries=disk_scan(a.root);ram=available();free=os.statvfs(a.root).f_bavail*os.statvfs(a.root).f_frsize
        admission=dict(available_RAM_bytes=ram,free_disk_bytes=free,owned_scratch_bytes=usage,disk_scan_retries=retries)
        need(ram>=2**40 and free>=2**40 and usage<270*GiB,'Separate available RAM/free-disk/scratch admission failed')
        with stdout.open('xb')as out,stderr.open('xb')as err:
            child=subprocess.Popen(cmd,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',GIT_OPTIONAL_LOCKS='0'),start_new_session=True)
            while child.poll()is None:
                time.sleep(5)
                if not samples or time.monotonic()-start-samples[-1]['seconds']>=30:
                    usage,retries=disk_scan(a.root)
                    row=dict(seconds=time.monotonic()-start,available_RAM_bytes=available(),owned_scratch_bytes=usage,disk_scan_retries=retries,cgroup=cgroup());samples.append(row)
                    temporary=a.live.with_suffix('.pending');temporary.write_text(json.dumps(row,indent=2)+'\n');os.replace(temporary,a.live)
                    need(row['available_RAM_bytes']>=256*GiB and usage<290*GiB,'Host RAM or campaign scratch reserve reached')
            code=child.wait()
    except BaseException as error:
        failure=type(error).__name__+': '+str(error)
    finally:
        # Finish the bounded termination and receipt step after a normal stop.
        # SIGKILL/host failure can still prevent a receipt and are not hidden.
        signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGTERM,signal.SIGINT})
        if child is not None and child.poll()is None:
            terminate_group(child.pid,signal.SIGTERM)
            try:code=child.wait(timeout=30)
            except subprocess.TimeoutExpired:terminate_group(child.pid,signal.SIGKILL);code=child.wait()
        try:final=cgroup()
        except BaseException as error:final=dict(unavailable=type(error).__name__+': '+str(error))
        result=dict(status='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'if code==0 and failure is None else'INCOMPLETE_NO_MATH_ACCEPTANCE',returncode=code,failure=failure,seconds=time.monotonic()-start,command=cmd,command_file_sha256=sha(a.command),supervisor_sha256=sha(Path(__file__)),before=before,final=final,samples=samples,admission=locals().get('admission'),stdout_sha256=sha(stdout)if stdout.exists()else None,stderr_sha256=sha(stderr)if stderr.exists()else None)
        publish(a.receipt,result)
    raise SystemExit(0 if result['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE' else 1)
if __name__=='__main__':main()
