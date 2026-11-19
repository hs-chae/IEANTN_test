import sys,os
BLOCK='/ryu/hyunsik/playground/independence/codex/ivy'
def deny_old_workspace(event,args):
    if event=='open'and args and isinstance(args[0],(str,bytes,os.PathLike)):
        value=os.fsdecode(args[0]);absolute=os.path.abspath(value)
        if absolute==BLOCK or absolute.startswith(BLOCK+'/'):raise PermissionError('ORIGINAL_WORKSPACE_OPEN_DENIED '+absolute)
sys.addaudithook(deny_old_workspace)
