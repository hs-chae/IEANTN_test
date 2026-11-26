#!/usr/bin/env python3
"""Recover exact original LOCK bytes from preserved snapshots/tool-write data.

No researcher script executes. The tiny interpreter permits literal strings,
string slicing/replace/index and in-memory Path read/write only. All recovered
bytes must match the already frozen cryptographic LOCK. Primary files stay read-only.
"""
import ast,hashlib,json,shlex
from pathlib import Path
import run_review as common
D=common.D
OUT=D/'exposure-supplemental-recovery-v1'

class VirtualPath(str):pass

def recorded_string_versions(events):
    files={};env={};history=[];seen=set()
    def value(node):
        if isinstance(node,ast.Constant) and isinstance(node.value,(str,int,type(None))):return node.value
        if isinstance(node,ast.Name):return env[node.id]
        if isinstance(node,ast.BinOp):
            a,b=value(node.left),value(node.right)
            if isinstance(node.op,ast.Add) and isinstance(a,str) and isinstance(b,str):return a+b
            if isinstance(node.op,ast.Div) and isinstance(a,VirtualPath) and isinstance(b,str):return VirtualPath(str(a).rstrip('/')+'/'+b)
        if isinstance(node,ast.Subscript) and isinstance(node.slice,ast.Slice):
            a=value(node.value);sl=node.slice
            if isinstance(a,str):return a[value(sl.lower) if sl.lower else None:value(sl.upper) if sl.upper else None:value(sl.step) if sl.step else None]
        if isinstance(node,ast.Call):
            if isinstance(node.func,ast.Name) and node.func.id=='Path':return VirtualPath(value(node.args[0]))
            if isinstance(node.func,ast.Attribute):
                a=value(node.func.value);method=node.func.attr;args=[value(x) for x in node.args]
                if isinstance(a,VirtualPath):
                    if method=='read_text' and not args:return files[str(a)]
                    if method=='write_text' and len(args)==1 and isinstance(args[0],str):files[str(a)]=args[0];return len(args[0])
                if isinstance(a,str) and method in ['replace','index'] and all(isinstance(x,(str,int)) for x in args):return getattr(a,method)(*args)
        raise ValueError('Outside pure recorded-string fragment')
    for raw in events.read_text().splitlines():
        event=json.loads(raw)
        if event.get('method')!='item/started':continue
        item=event.get('params',{}).get('item',{});key=item.get('id')
        if item.get('type')!='commandExecution' or key in seen:continue
        seen.add(key);command=item.get('command','')
        try:
            parts=shlex.split(command)
            if len(parts)==3 and parts[1]=='-c':command=parts[2]
        except ValueError:continue
        if "<<'PY'\n" not in command:continue
        code=command.split("<<'PY'\n",1)[1].split('\nPY',1)[0]
        try:tree=ast.parse(code)
        except SyntaxError:continue
        for stmt in tree.body:
            try:
                if isinstance(stmt,ast.Assign) and len(stmt.targets)==1 and isinstance(stmt.targets[0],ast.Name):env[stmt.targets[0].id]=value(stmt.value)
                elif isinstance(stmt,ast.Expr):value(stmt.value)
            except (ValueError,KeyError,TypeError,AttributeError):continue
        for path,text in files.items():
            if path.endswith(('.lean','.md')):history.append(dict(recorded_path=path,bytes=text.encode(),command_id=key,command_sha256=hashlib.sha256(command.encode()).hexdigest()))
    return history


def main():
    common.need(not OUT.exists(),'Fresh recovery directory required');OUT.mkdir()
    plan_path=D/'EXPOSURE_CENSORED_SUPPLEMENTAL_PLAN.json';plan=common.load(plan_path);primary=D/'exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json';primary_sha=common.sha(primary);rows=[]
    for row in plan['rows']:
        trial=row['trial'];root=D/'exposure-controller-v2/trials'/trial/'research-v1';lock=root/'submission/LOCK.json';common.need(common.sha(lock)==row['lock_sha256'],'Original lock differs from preflight')
        target=OUT/trial;target.mkdir();(target/'LOCK.json').write_bytes(lock.read_bytes());artifacts=[];versions=None
        for item in common.load(lock)['files']:
            name=item['path'];common.need(name==Path(name).name,'Invalid locked file name');original=root/'submission'/name
            matches=[p for p in root.rglob(name) if p.is_file() and not p.is_symlink() and common.sha(p)==item['sha256']]
            if matches:
                chosen=original if original in matches else sorted(matches)[0];data=chosen.read_bytes();provenance=dict(kind='ORIGINAL_PRIMARY_EXACT' if chosen==original else 'PRESERVED_ORIGINAL_SNAPSHOT_EXACT',origin=str(chosen),all_matching_snapshots=[str(p) for p in sorted(matches)])
            else:
                if versions is None:versions=recorded_string_versions(root/'events.jsonl')
                candidates=[v for v in versions if Path(v['recorded_path']).name==name and hashlib.sha256(v['bytes']).hexdigest()==item['sha256']]
                common.need(candidates,'No exact LOCK bytes recoverable for '+trial+'/'+name);v=candidates[0];data=v['bytes'];provenance={k:value for k,value in v.items() if k!='bytes'};provenance.update(kind='ORIGINAL_RECORDED_STRING_TRANSFORMS_EXACT',events=str(root/'events.jsonl'),events_sha256=common.sha(root/'events.jsonl'))
            common.need(hashlib.sha256(data).hexdigest()==item['sha256'],'Recovered byte hash differs');(target/name).write_bytes(data)
            artifacts.append(dict(path=name,sha256=item['sha256'],bytes=len(data),recovered_from=provenance,original_submission_present=original.is_file(),original_submission_sha256=common.sha(original) if original.is_file() else None))
        rows.append(dict(trial=trial,primary_eligible=False,lock_sha256=common.sha(lock),recovered_directory=str(target),artifacts=artifacts))
    common.need(common.sha(primary)==primary_sha,'Original primary summary changed')
    common.save(OUT/'RESULT.json',dict(status='ALL13_ORIGINAL_LOCK_PAYLOADS_RECOVERED_EXACT_BYTES_NO_PRIMARY_RECLASSIFICATION',rows=rows,primary_summary_sha256=primary_sha,preflight_sha256=common.sha(plan_path),controller_sha256=common.sha(Path(__file__)),researcher_code_executed_on_host=False,original_evidence_modified=False))
    print('PASS all13 exact originalLOCK payload bytes recovered; primaryinadmissibility unchanged')

if __name__=='__main__':main()
