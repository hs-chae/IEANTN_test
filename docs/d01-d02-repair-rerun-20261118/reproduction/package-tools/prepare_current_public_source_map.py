"""Exact source addressing for public reproduction, without source/math changes."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
A=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('source_inventory',A/'prepare_inventory.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--inventory',type=Path,required=True);p.add_argument('--selection',type=Path,action='append',default=[]);p.add_argument('--out',type=Path,required=True);a=p.parse_args();m.need(not a.out.exists(),'fresh source map');files={};changes=[];inputs=[]
 inv=m.load(a.inventory);rows=[{'path':z['source_path'],'sha256':z['sha256'],'bytes':z['size'],'archive_path':z['archive_path'],'gzip_json':z['gzip_json']}for z in inv['assets']];inputs.append({'path':str(a.inventory.resolve()),'sha256':sha(a.inventory)})
 for q in a.selection:
  x=m.load(q);m.need(isinstance(x.get('assets'),list),'exact explicit selected asset list');rows.extend(x['assets']);inputs.append({'path':str(q.resolve()),'sha256':sha(q)})
 for z in rows:
  # The outer archive manifest pins the source-map artifact itself; no recursive self hash.
  if z['archive_path']=='PUBLIC_SOURCE_MAP.json':continue
  m.safe_name(z['archive_path']);original=Path(z['path']);m.need(original.is_file() and not original.is_symlink(),'selected ordinary original source');m.need(type(z.get('gzip_json',False))is bool,'explicit source-map compression flag');src=original.resolve();h=sha(src);n=src.stat().st_size
  if h!=z['sha256']or n!=z['bytes']:changes.append({'path':str(src),'previous_sha256':z['sha256'],'current_sha256':h,'previous_bytes':z['bytes'],'current_bytes':n,'requires_current_final_inventory_and_source_gates_not_silent_acceptance':True})
  entry={'public_path':z['archive_path'],'sha256':h,'bytes':n,'individual_gzip_in_outer_archive':z.get('gzip_json',False),'restored_original_path_on_unpack':True};key=str(src)
  if key in files:m.need(files[key]['sha256']==h and files[key]['bytes']==n,'same original source has inconsistent actual bytes')
  if key not in files or (not files[key]['public_path'].startswith('evidence/') and entry['public_path'].startswith('evidence/')):files[key]=entry
 value={'schema':'EXPLICIT_ORIGINAL_TO_PUBLIC_SOURCE_PATH_MAP_V1','status':'CURRENT_EXPLICIT_SOURCE_ADDRESS_MAP_NOT_MATHEMATICAL_OR_PUBLICATION_APPROVAL','input_selections':inputs,'source_map_self_is_pinned_by_outer_manifest_not_self_mapped':True,'rules':'Resolve exact original path only; verify public file SHA and length before use. Individually compressed JSON originals are restored by the reconstructor. All current mathematical/source/metadata and final-publication gates remain mandatory.','current_byte_changes_since_preliminary_selection':changes,'files':files}
 with a.out.open('x')as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'status':value['status'],'original_source_paths':len(files),'explicit_current_byte_changes':len(changes),'sha256':sha(a.out)},sort_keys=True))
if __name__=='__main__':main()
