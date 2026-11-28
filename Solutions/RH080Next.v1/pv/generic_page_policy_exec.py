#!/usr/bin/env python3
"""Set a documented process-only page policy, verify it, and exec an argv.

This records a pre-exec resource observation, never child success or a proof.
No global THP setting or other existing process is changed.
"""
import argparse,ctypes,hashlib,json,os,re,time
from pathlib import Path


def need(ok,message):
    if not ok:raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fresh_atomic(path,value):
    temporary=path.with_name('.'+path.name+'.'+str(os.getpid())+'.tmp')
    descriptor=os.open(temporary,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
    try:
        with os.fdopen(descriptor,'w')as stream:
            json.dump(value,stream,indent=2,allow_nan=False);stream.write('\n');stream.flush();os.fsync(stream.fileno())
        os.link(temporary,path)
    finally:
        temporary.unlink()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--disable-thp',action='store_true',required=True)
    ap.add_argument('--receipt',required=True,type=Path)
    ap.add_argument('command',nargs=argparse.REMAINDER)
    a=ap.parse_args();command=a.command[1:]if a.command[:1]==['--']else a.command
    need(a.disable_thp and command,'Explicit process policy and nonempty executable argv required')
    executable=Path(command[0]);need(executable.is_absolute()and executable.is_file()and os.access(executable,os.X_OK),'Absolute existing executable required')
    need(a.receipt.parent.is_dir()and not os.path.lexists(a.receipt),'Existing receipt directory and fresh receipt required')
    header=Path('/usr/include/linux/prctl.h');raw=header.read_bytes();text=raw.decode()
    constants={name:int(re.search(r'^#define\s+'+name+r'\s+(\d+)\s*$',text,re.M)[1])for name in['PR_SET_THP_DISABLE','PR_GET_THP_DISABLE']}
    need(constants==dict(PR_SET_THP_DISABLE=41,PR_GET_THP_DISABLE=42),'Unexpected Linux UAPI page-policy constants')
    function=ctypes.CDLL(None,use_errno=True).prctl
    function.argtypes=[ctypes.c_int,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong];function.restype=ctypes.c_int
    before=function(constants['PR_GET_THP_DISABLE'],0,0,0,0)
    if before<0:raise OSError(ctypes.get_errno(),'PR_GET_THP_DISABLE failed')
    if function(constants['PR_SET_THP_DISABLE'],1,0,0,0)<0:raise OSError(ctypes.get_errno(),'PR_SET_THP_DISABLE failed')
    after=function(constants['PR_GET_THP_DISABLE'],0,0,0,0)
    status=Path('/proc/self/status').read_text();enabled=next((line.split(':',1)[1].strip()for line in status.splitlines()if line.startswith('THP_enabled:')),None)
    need(after==1 and enabled=='0','Process page policy was not verified by prctl and proc status')
    value=dict(status='VERIFIED_PROCESS_PAGE_POLICY_BEFORE_EXEC_NOT_CHILD_OR_PROOF_ACCEPTANCE',policy='PROCESS_THP_DISABLED',PID=os.getpid(),PR_GET_before=before,PR_GET_after=after,proc_THP_enabled=enabled,actual_affinity=sorted(os.sched_getaffinity(0)),command=command,local_header_sha256=hashlib.sha256(raw).hexdigest(),local_header_constants=constants,wrapper_sha256=sha(Path(__file__)),host_global_settings_written=False,other_existing_processes_modified=False,time_UTC=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    fresh_atomic(a.receipt,value)
    os.execv(command[0],command)


if __name__=='__main__':main()
