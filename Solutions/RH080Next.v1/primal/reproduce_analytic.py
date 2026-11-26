#!/usr/bin/env python3
"""Compile pure-Mathlib primal lemmas in a fresh directory, strictly audit axioms.

LEAN_PATH must contain only the pinned generic dependency builds. This script
never calls native_decide and does not label these kernel-only proofs as PV.
"""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--compiler',type=Path,required=True);ap.add_argument('--generic-lean-path',required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);here=Path(__file__).resolve().parent;names=['GaussianDilation','ChordQuadrature'];frozen=a.out/'source';objects=a.out/'objects';logs=a.out/'logs'
 for p in [frozen,objects,logs]:p.mkdir()
 compiler=a.compiler.resolve(strict=True);version=subprocess.check_output([str(compiler),'--version'],text=True).strip();need('4.34.0-rc2'in version,'Pinned Lean4.34.0-rc2 required');env=dict(os.environ,LEAN_PATH=a.generic_lean_path);rows=[];began=time.monotonic();allowed={'propext','Classical.choice','Quot.sound'}
 for name in names:
  source=here/(name+'.lean');target=frozen/source.name;shutil.copy2(source,target);before=sha(source);expected=target.read_text().count('#print axioms');need(expected>0,'Missing declaration audits');cmd=['/usr/bin/time','-v','-o',str((logs/(name+'.time')).resolve()),str(compiler),'-j','1','-o',str((objects/(name+'.olean')).resolve()),target.name];t=time.monotonic()
  p=subprocess.run(cmd,cwd=frozen,env=env,text=True,capture_output=True);(logs/(name+'.stdout')).write_text(p.stdout);(logs/(name+'.stderr')).write_text(p.stderr);audits=re.findall(r'depends on axioms: \[([^\]]*)\]',p.stdout);metrics=(logs/(name+'.time')).read_text();peaks=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',metrics);artifact=objects/(name+'.olean');valid=p.returncode==0 and len(audits)==expected and all({x.strip()for x in row.split(',')if x.strip()}<=allowed for row in audits) and len(peaks)==1 and artifact.is_file() and sha(source)==before
  row={'module':name,'accepted':valid,'returncode':p.returncode,'command':cmd,'seconds':time.monotonic()-t,'source_sha256':before,'object_sha256':sha(artifact)if artifact.is_file()else None,'axiom_audits':len(audits),'expected_audits':expected,'peak_RSS_KiB':int(peaks[0])if len(peaks)==1 else None};rows.append(row);print(json.dumps(row),flush=True)
  if not valid:
   (a.out/'FAILED.json').write_text(json.dumps({'status':'FAILED_NO_ACCEPTANCE','rows':rows},indent=2)+'\n');raise ValueError('Compilation/audit failed; preserved logs')
 result={'status':'PASS_KERNEL_ANALYTIC_LEMMAS_STD3_NOT_SOURCE_FIRST_PV','compiler_sha256':sha(compiler),'compiler_version':version,'generic_lean_path':a.generic_lean_path,'script_sha256':sha(Path(__file__)),'python':sys.version,'rows':rows,'seconds':time.monotonic()-began};temp=a.out/'RESULT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.out/'RESULT.json');temp.unlink()
if __name__=='__main__':main()
