"""Check or remove the one sealed regenerable final-bundle reproduction clone."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,stat,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[1]
BASE=R/'reproduction/apply_final24_regenerable_cleanup.py'
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
need(sha(BASE)=='e959ab361ca4f7a93b05d0098b5142e95dd24f7770425f3c8ca1c6f94b9b3e7f','reviewed base guards unchanged')
spec=importlib.util.spec_from_file_location('reviewed_cleanup_base',BASE);base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--apply',action='store_true');a=p.parse_args()
preview=R/'evidence/FINAL24_ACTUAL_FINAL_BUNDLE_FRESH_ROOT_CLEANUP_PREVIEW_V1.json'
need(sha(preview)=='a808de64f9ab8e8ee7b737dc79f0c6b84300a317ce49e73560efee9b3ca67e7e','exact one-tree preview')
v=base.load(preview);root=base.original(v['target']);need(root.parent==Path('/data')and root.name.startswith('ivy-final24-actual-bundle-repro-')and root.stat().st_uid==os.getuid(),'only owned reproduction clone')
for key in ['essential_retained_manifest','complete_actual_clean_verification','canonical_primary_manifest','canonical_primary_archive']:
    ref=v[key];q=Path(ref['path']);need(not q.is_relative_to(root)and q.is_file()and sha(q)==ref['sha256']and q.stat().st_size==ref['bytes'],'retained evidence/canonical source changed')
success=base.load(v['complete_actual_clean_verification']['path']);need(success['status'].startswith('PASS_')and success['actual_fresh_root']==str(root),'actual completed clean suite and exact root')
for ref in base.load(v['essential_retained_manifest']['path'])['files']:
    q=Path(ref['path']);need(not q.is_relative_to(root)and q.is_file()and sha(q)==ref['sha256']and q.stat().st_size==ref['bytes'],'every essential source and receipt retained')
base.no_mount(root,base.mounts());expected={z['relative_path']:z for z in v['files']};actual={};dirs=[]
for q in root.rglob('*'):
    base.original(q)
    if q.is_dir():dirs.append(q)
    else:need(q.is_file(),'regular clone entries only');actual[str(q.relative_to(root))]=q
need(set(actual)==set(expected)and{str(q.relative_to(root))for q in dirs}==set(v['directories'])and len(actual)==8772,'whole exact unchanged file/directory census')
def unchanged(q,z):
    s=q.stat();need(stat.S_ISREG(s.st_mode)and s.st_size==z['bytes']and s.st_nlink==z['hardlink_count']and stat.S_IMODE(s.st_mode)==z['mode']and sha(q)==z['sha256'],'exact regenerable file unchanged')
for name,q in actual.items():unchanged(q,expected[name])
for proc in Path('/proc').glob('[0-9]*'):
    if int(proc.name)==os.getpid():continue
    try:cmd=(proc/'cmdline').read_bytes();maps=(proc/'maps').read_bytes()
    except(FileNotFoundError,ProcessLookupError,PermissionError):continue
    need(str(root).encode()not in cmd and str(root).encode()not in maps,'live process still names clone')
    try:links=[proc/'cwd']+list((proc/'fd').iterdir())
    except(FileNotFoundError,ProcessLookupError,PermissionError):continue
    for link in links:
        try:value=os.readlink(link)
        except(OSError,PermissionError):continue
        need(value!=str(root)and not value.startswith(str(root)+'/'),'live cwd/file still uses clone')
if not a.apply:print('PASS_EXACT_FINAL_CLONE_ALL_BYTES_RETAINED_EVIDENCE_NO_LIVE_USERS_NO_DELETION');raise SystemExit(0)
out=R/'evidence/ACTUAL_FINAL_BUNDLE_REGENERABLE_FRESH_ROOT_CLEANUP_RECEIPT.json';need(not out.exists(),'fresh actual cleanup receipt')
receipt={'status':'STARTED_EXACT_SEALED_REGENERABLE_CLONE_CLEANUP','preview_sha256':sha(preview),'helper_sha256':sha(Path(__file__)),'target':str(root),'removed_files':0,'deleted_payload_bytes':0,'deleted_allocated_regular_bytes':0,'error':None,'canonical_source_archive_parts_proofs_certificates_locked_inputs_and_essential_receipts_deleted':False}
def save():
    temporary=out.with_suffix('.pending');temporary.write_text(json.dumps(receipt,indent=2)+'\n');temporary.replace(out)
save()
try:
    for name,q in actual.items():
        z=expected[name];unchanged(q,z);blocks=q.stat().st_blocks*512;q.unlink();receipt['removed_files']+=1;receipt['deleted_payload_bytes']+=z['bytes'];receipt['deleted_allocated_regular_bytes']+=blocks
    for q in sorted(dirs+[root],key=lambda x:len(x.parts),reverse=True):base.no_mount(q,base.mounts());q.rmdir()
    receipt['status']='PASS_ONLY_EXACT_COMPLETED_REPRODUCTION_CLONE_REMOVED_ALL_ESSENTIAL_EVIDENCE_RETAINED'
except BaseException as error:receipt['status']='PARTIAL_EXACT_CLONE_CLEANUP_RECORDED';receipt['error']=type(error).__name__+': '+str(error);raise
finally:save()
print(json.dumps(receipt,sort_keys=True))
