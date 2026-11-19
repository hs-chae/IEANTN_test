"""Read-only exact original-to-public source resolution; no mathematical execution.

With neither environment variable, original experiment paths are used. Portable
mode requires both IEANTN_SOURCE_ROOT and IEANTN_SOURCE_MAP. Every mapped read
checks the original SHA256 and size. Missing original-workspace mappings fail;
there is no path search or fallback to the original workspace in portable mode.
"""
from pathlib import Path, PurePosixPath
import hashlib,json,math,os
ORIGINAL_WORKSPACE=Path('/ryu/hyunsik/playground/independence/codex/ivy')
ORIGINAL_STUDY=ORIGINAL_WORKSPACE/'ieantn-d01-d02-repair-rerun-20261118'
def need(ok,msg):
    if not ok:raise ValueError(msg)
def strict_load(data):
    def pairs(items):
        out={}
        for key,value in items:
            need(key not in out,'DUPLICATE_SOURCE_MAP_KEY '+key);out[key]=value
        return out
    def bad(v):raise ValueError('NONFINITE_SOURCE_MAP_JSON '+v)
    def finite(v):
        value=float(v);need(math.isfinite(value),'NONFINITE_SOURCE_MAP_FLOAT');return value
    return json.loads(data,object_pairs_hook=pairs,parse_constant=bad,parse_float=finite)
_root=os.environ.get('IEANTN_SOURCE_ROOT');_map=os.environ.get('IEANTN_SOURCE_MAP')
need(bool(_root)==bool(_map),'PORTABLE_SOURCE_ROOT_AND_MAP_REQUIRED_TOGETHER')
ROOT=Path(_root).resolve()if _root else None
MAP_PATH=Path(_map).resolve()if _map else None
MAP=strict_load(MAP_PATH.read_bytes())if MAP_PATH else None
if MAP is not None:
    need(MAP.get('schema')=='EXPLICIT_ORIGINAL_TO_PUBLIC_SOURCE_PATH_MAP_V1'and isinstance(MAP.get('files'),dict),'EXACT_PUBLIC_SOURCE_MAP_SCHEMA')
    for old,rec in MAP['files'].items():
        need(isinstance(old,str)and Path(old).is_absolute()and isinstance(rec,dict),'SOURCE_MAP_RECORD_SCHEMA')
        rel=rec.get('public_path');need(isinstance(rel,str),'SOURCE_MAP_PUBLIC_PATH_STRING');q=PurePosixPath(rel)
        need(not q.is_absolute()and q.parts and all(x not in ['', '.', '..']for x in q.parts)and str(q)==rel,'CANONICAL_PUBLIC_SOURCE_PATH')
        need(isinstance(rec.get('sha256'),str)and len(rec['sha256'])==64 and all(c in '0123456789abcdef'for c in rec['sha256']),'SOURCE_MAP_SHA256')
        need(type(rec.get('bytes'))is int and rec['bytes']>=0,'SOURCE_MAP_EXACT_SIZE')
def source_path(value):
    p=Path(value)
    if MAP is None:return p
    rec=MAP['files'].get(str(p))
    if rec is None:
        need(not p.is_relative_to(ORIGINAL_WORKSPACE)and not str(p).startswith('/data/ivy-d01-d02-portable-'),'MISSING_EXACT_PUBLIC_SOURCE_MAPPING '+str(p))
        need(p.resolve().is_relative_to(ROOT),'UNMAPPED_LOCAL_DATA_OUTSIDE_PUBLIC_ROOT '+str(p))
        return p
    actual=(ROOT/rec['public_path']).resolve();need(actual.is_relative_to(ROOT),'PUBLIC_SOURCE_PATH_ESCAPES_ROOT')
    data=actual.read_bytes();need(len(data)==rec['bytes']and hashlib.sha256(data).hexdigest()==rec['sha256'],'PUBLIC_SOURCE_ORIGINAL_SHA_OR_SIZE '+str(p))
    return actual
def read_bytes(value):return source_path(value).read_bytes()
def source_is_file(value):
    if MAP is not None and str(Path(value))in MAP['files']:return source_path(value).is_file()
    if MAP is not None and Path(value).is_relative_to(ORIGINAL_WORKSPACE):return False
    return source_path(value).is_file()
def physical_relative_files(directory):
    # A source LOCK.json supplies the exact public directory, preserving its
    # relative filenames. The actual physical census remains independent of
    # the selected map entries and catches unexpected/missing payload files.
    marker=source_path(Path(directory)/'LOCK.json');root=marker.parent
    return {str(p.relative_to(root))for p in root.rglob('*')if p.is_file()}
