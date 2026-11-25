#!/usr/bin/env python3
"""Literal and concrete output diagnostics; does not assume I/O success."""
import hashlib, json, os, pathlib, subprocess

here=pathlib.Path(__file__).resolve().parent
source=here.parents[1]/'pv/dual_grid.c'
exe=here/'dual_grid_diagnostic'
def need(ok,message):
    if not ok:raise RuntimeError(message)
need(b'printf("%llu\\n", (unsigned long long)rh_dual_bound());' in source.read_bytes(),'Physical format bytes or cast differ')
subprocess.run(['cc','-std=c11','-O2','-Wall','-Wextra','-Werror',str(source),'-o',str(exe)],check=True,capture_output=True)
normal=subprocess.run([str(exe)],capture_output=True)
need(normal.returncode==0 and normal.stdout==b'1221161\n','Normal actual stdout differs')
bad=None
if pathlib.Path('/dev/full').is_char_device():
    with open('/dev/full','wb') as output:
        failed_output=subprocess.run([str(exe)],stdout=output,stderr=subprocess.PIPE)
    bad=dict(destination='/dev/full',returncode=failed_output.returncode,stderr_hex=failed_output.stderr.hex(),meaning='Main ignores printf/exit-flush failure; exit zero does not establish delivered stdout.')
context=json.loads(pathlib.Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text())
env=os.environ.copy();env['LEAN_PATH']=str(here/'fresh-replay/objects')+':'+context['generic_lean_path']
command=[context['compiler'],'-j2','--root='+str(here),'-o',str(here/'LiteralAudit.olean'),str(here/'LiteralAudit.lean')]
checked=subprocess.run(command,env=env,capture_output=True)
(here/'LiteralAudit.stdout').write_bytes(checked.stdout)
(here/'LiteralAudit.stderr').write_bytes(checked.stderr)
need(checked.returncode==0,'Literal audit rejected: '+checked.stdout.decode(errors='replace'))
result=dict(status='PASS_LITERAL_AND_ACTUAL_OUTPUT_DIAGNOSTICS_WITH_EXPLICIT_IO_FAILURE_BOUNDARY',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),normal_returncode=normal.returncode,normal_stdout_hex=normal.stdout.hex(),failed_output=bad,literal_lean_command=command,source_first_PV=False)
(here/'io_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
