from pathlib import Path
from types import SimpleNamespace
import importlib.util,json,sys
sys.dont_write_bytecode=True
root=Path(sys.argv[1]);study=root/'ieantn-d01-d02-repair-rerun-20261118'
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
m=module('actual_final24_f16',study/'scripts/run_portable_numerical_reproduction_relocated_v2.py')
m.configure_relocation(SimpleNamespace(source_root=root,relocation_config=root/'portable/RELOCATION_CONFIG.json',resource_registry_root=Path(sys.argv[2])))
q=module('actual_frozen_capacity',m.CAPACITY).configured()
if not callable(q.reserve_one)or not callable(q.resources.host_available):raise ValueError('full frozen resource dependency closure unavailable')
if any('site-packages'in str(getattr(value,'__file__',''))for value in sys.modules.values()):raise ValueError('non-stdlib site package unexpectedly imported')
print(json.dumps({'status':'PASS_FULL_NUMERICAL_CONTROLLER_RESOURCE_IMPORT_CLOSURE_WITH_SITE_DISABLED','source_root':str(root),'interpreter':sys.executable,'python_version':sys.version.split()[0],'site_enabled':False,'model_or_scope_or_reservation_or_numerical_calls':0}))
