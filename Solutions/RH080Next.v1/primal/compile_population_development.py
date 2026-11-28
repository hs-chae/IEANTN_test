#!/usr/bin/env python3
"""Development compilation, explicit previously proved source-object reuse disclosed."""
import argparse,json,os,pathlib,subprocess,time,hashlib
D=pathlib.Path('/data/ivy-rh080-next-20261125'); R=D/'network'; S=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('modules',nargs='*');a=p.parse_args()
out=D/'primal-runs/population-canonical-dev-v1';out.mkdir(exist_ok=True)
ctx=json.loads((out/'DEV_CONTEXT.json').read_text());obj=pathlib.Path(ctx['objects'])
mods=[('IEANTN.Vocabulary.Zeta',R/'IEANTN/Vocabulary/Zeta.lean'),('IEANTN.Vocabulary.ZeroFreeHalfPlane',R/'IEANTN/Vocabulary/ZeroFreeHalfPlane.lean'),('IEANTN.Nodes.RH.v1.Conclusions',R/'IEANTN/Nodes/RH/v1/Conclusions.lean'),('IEANTN.Vocabulary.CMSFunctional',R/'IEANTN/Vocabulary/CMSFunctional.lean'),('IEANTN.Vocabulary.AffineFourierWindow',R/'IEANTN/Vocabulary/AffineFourierWindow.lean'),('IEANTN.Nodes.BRFourierInput.v1.Conclusions',R/'IEANTN/Nodes/BRFourierInput/v1/Conclusions.lean'),('IEANTN.Nodes.AffineFourierPrograms.v1.Tables',R/'IEANTN/Nodes/AffineFourierPrograms/v1/Tables.lean'),('IEANTN.Nodes.AffineFourierPrograms.v1.Conclusions',R/'IEANTN/Nodes/AffineFourierPrograms/v1/Conclusions.lean'),('IEANTN.Nodes.RHWeightedPopulation.v1.Conclusions',R/'IEANTN/Nodes/RHWeightedPopulation/v1/Conclusions.lean')]
mods += [(n,S/'population'/(n+'.lean')) for n in ['BRSourceInterfaces','AffineProgramsSolution','WeightedPopulationSolution','PopulationActualConsumers','PopulationMatchedControl','PopulationCanonicalAudit']]
if a.modules: mods=[x for x in mods if x[0] in a.modules]
env=os.environ.copy();env['LEAN_PATH']=ctx['lean_path']
for mod,src in mods:
 if not src.exists(): continue
 target=obj/(mod.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 root=R if mod.startswith('IEANTN.') else S/'population'
 t=time.monotonic();p=subprocess.run(['/usr/bin/time','-v',ctx['compiler'],'-j1','--root='+str(root),'-o',str(target),str(src)],env=env,text=True,capture_output=True)
 (out/(mod.replace('.','_')+'.stdout')).write_text(p.stdout);(out/(mod.replace('.','_')+'.stderr')).write_text(p.stderr)
 print(mod,p.returncode,p.stdout[-5000:],p.stderr[-1000:] if p.returncode else '',flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 (out/(mod.replace('.','_')+'.DEVELOPMENT.json')).write_text(json.dumps(dict(status='DEVELOPMENT_COMPILED_SOURCE_OBJECT_REUSE',module=mod,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),object_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),seconds=time.monotonic()-t),indent=2)+'\n')
