#!/usr/bin/env python3
"""Create a pinned generic-only compiler context without application objects."""
from __future__ import annotations
import argparse,hashlib,json,os,platform,shutil,signal,subprocess,sys,tempfile,time
from pathlib import Path

PROJECT=Path(__file__).resolve().parents[1]
REPOSITORY=PROJECT.parents[1]
COMPILER_SHA256="e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
TOOLCHAIN="leanprover/lean4:v4.34.0-rc2"
PINS=[
 ("mathlib","71a80585ee495fc24472fd0eaffc89d94e4fd8d6"),
 ("plausible","d9598f07b1bc701f1e3aae163d2681c1fd978793"),
 ("LeanSearchClient","ba67e212be1197b84c1f1f6299488a10a3002713"),
 ("importGraph","1681d78dd6e65e38b143f9740d829c826673807c"),
 ("proofwidgets","a8acbfd87375ff4abe14ce09db5b7664d383bc7f"),
 ("aesop","18889deb9e83ea7420ef51c160d6f88552e744e3"),
 ("Qq","507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3"),
 ("batteries","4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb"),
]
DEPENDENCIES=[dict(name=n,revision=r)for n,r in PINS]
CLI_PIN="ab3a82db9fea14cf0fd7f5a2de650f4b534640af"
CLI_URL="https://github.com/leanprover/lean4-cli"
FETCH_FREE_DISK_BYTES=32*2**30
FETCH_TIMEOUT_SECONDS=7200
PUBLIC_FETCH_CREDENTIAL_NAMES=("AZURE_BEARER_TOKEN","AZURE_STORAGE_SAS_TOKEN",
    "AZURE_STORAGE_KEY","AZURE_STORAGE_CONNECTION_STRING","AZURE_CLIENT_SECRET",
    "SAS_TOKEN","GH_TOKEN","GITHUB_TOKEN")
_fetch_deadline=None

def need(value,message):
    if not value:raise ValueError(message)

def sha(path):
    h=hashlib.sha256()
    with Path(path).open("rb")as f:
        for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
    return h.hexdigest()

def read_json(path):
    def pairs(items):
        d={}
        for k,v in items:
            need(k not in d,"Duplicate JSON key "+k);d[k]=v
        return d
    def bad(value):raise ValueError("Nonfinite JSON "+value)
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=bad)

def atomic(path,value):
    path=Path(path);need(not os.path.lexists(path),"Fresh output required: "+str(path))
    path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix="."+path.name+"-",dir=path.parent)
    try:
        with os.fdopen(fd,"w")as f:
            json.dump(value,f,indent=2,allow_nan=False);f.write("\n");f.flush();os.fsync(f.fileno())
        os.link(tmp,path)
    finally:Path(tmp).unlink()

def command(args,*,cwd=None,env=None):
    args=[str(x)for x in args]
    if env is None:env=dict(os.environ,GIT_OPTIONAL_LOCKS="0")
    remaining=120 if _fetch_deadline is None else _fetch_deadline-time.monotonic()
    need(remaining>0,"Overall fetch deadline expired before command: "+repr(args))
    child=subprocess.Popen(args,cwd=cwd,env=env,text=True,stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    try:
        stdout,stderr=child.communicate(timeout=remaining)
    except BaseException:
        # Every command owns a new session; descendants inherit this group.
        # Kill the group even when its leader has exited but a child holds pipes.
        try:os.killpg(child.pid,signal.SIGTERM)
        except ProcessLookupError:pass
        try:child.communicate(timeout=2)
        except subprocess.TimeoutExpired:pass
        # A descendant may close its output pipes and survive SIGTERM even
        # after communicate returns. Always finish the owned group with KILL.
        try:os.killpg(child.pid,signal.SIGKILL)
        except ProcessLookupError:pass
        try:child.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            raise ValueError("Owned command group did not drain after termination: "+repr(args))
        raise
    need(child.returncode==0,"Command failed: "+repr(args)+"\n"+stderr[-4000:])
    return stdout.strip()

def fetch_environment(workspace,compiler):
    # Do not inherit endpoint/scope/upload credentials or Git redirections.
    env={k:v for k,v in os.environ.items()
        if not k.startswith(("MATHLIB_CACHE_","LAKE_","GIT_","GCM_"))}
    for key in ("LEAN_PATH","LEAN_SRC_PATH",*PUBLIC_FETCH_CREDENTIAL_NAMES):env.pop(key,None)
    env.update(PATH=str(compiler.parent)+os.pathsep+os.environ.get("PATH",""),
        ELAN_TOOLCHAIN=TOOLCHAIN,PYTHONDONTWRITEBYTECODE="1",
        MATHLIB_CACHE_DIR=str(workspace/"cache"/"mathlib"),
        LAKE_CACHE_DIR=str(workspace/"cache"/"lake"),
        XDG_CACHE_HOME=str(workspace/"cache"),XDG_CONFIG_HOME=str(workspace/"config"),
        CURL_HOME=str(workspace/"curl-home"),GIT_OPTIONAL_LOCKS="0",
        GIT_TERMINAL_PROMPT="0",GIT_ASKPASS="/bin/false",SSH_ASKPASS="/bin/false",
        GCM_INTERACTIVE="Never",GIT_CONFIG_NOSYSTEM="1",
        GIT_CONFIG_GLOBAL="/dev/null",GIT_CONFIG_SYSTEM="/dev/null")
    return env

def manifest_pins(mathlib):
    path=mathlib/"lake-manifest.json";manifest=read_json(path)
    packages=manifest["packages"];names=[r["name"]for r in packages]
    need(len(names)==len(set(names)),"Duplicate generic manifest package")
    locked={r["name"]:r for r in packages}
    need(set(locked)=={n for n,_ in PINS[1:]}|{"Cli"},"Unexpected generic manifest dependency set")
    for name,rev in PINS[1:]:
        need(locked[name].get("rev")==rev,"Pinned Mathlib manifest differs: "+name)
    cli=locked["Cli"]
    need(cli.get("rev")==CLI_PIN and cli.get("url")==CLI_URL and cli.get("type")=="git",
        "Pinned build-time Cli manifest identity differs")
    return dict(manifest_sha256=sha(path),
        supplemental_build_dependency=dict(name="Cli",revision=CLI_PIN,url=CLI_URL,
            included_in_eight_compiled_generic_roots=False))

def available_disk(path):
    while not path.exists():path=path.parent
    return dict(measured_path=str(path),free_bytes=shutil.disk_usage(path).free,
        minimum_admission_bytes=FETCH_FREE_DISK_BYTES,
        admission_is_not_an_upper_bound_on_downloads_or_disk_use=True)

def validate_context(c,*,env=None):
    need(c.get("generic_dependencies")==DEPENDENCIES,"Exact eight generic pins/order required")
    compiler=Path(c["compiler"]).resolve(strict=True)
    need(compiler.is_file()and sha(compiler)==c.get("compiler_sha256")==COMPILER_SHA256,
        "Compiler bytes differ from pinned Linux Lean4.34.0-rc2")
    version=command([compiler,"--version"],env=env)
    need(version==c.get("compiler_version")and "4.34.0-rc2"in version,
        "Compiler version differs")
    roots=c["generic_lean_path"].split(":")
    need(len(roots)==len(set(roots))==8,"Eight distinct generic object roots required")
    rows=[]
    for raw,(name,revision)in zip(roots,PINS):
        root=Path(raw).resolve(strict=True)
        need(root.is_dir()and root.parts[-4:]==(".lake","build","lib","lean"),
            "Unsupported generic object-root layout")
        repo=root.parents[3]
        need(repo.name==name,"Generic object root/order differs: "+name)
        need(command(["git","-C",repo,"rev-parse","HEAD"],env=env)==revision,"Generic revision differs: "+name)
        need(not command(["git","-C",repo,"status","--porcelain","--untracked-files=no"],env=env),
            "Generic tracked source is dirty: "+name)
        rows.append(dict(name=name,revision=revision,source_root=str(repo),object_root=str(root)))
    return dict(compiler=str(compiler),compiler_sha256=COMPILER_SHA256,
        compiler_version=version,generic_lean_path=":".join(r["object_root"]for r in rows),
        generic_dependencies=DEPENDENCIES),rows

def resolve_compiler(value):
    if value:return Path(value).resolve(strict=True)
    elan=shutil.which("elan")
    if elan:return Path(command([elan,"which","lean"],env=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN))).resolve(strict=True)
    lean=shutil.which("lean");need(lean,"Provide --compiler for the exact pinned toolchain")
    return Path(lean).resolve(strict=True)

def main():
    global _fetch_deadline
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--output",required=True,type=Path)
    sources=ap.add_mutually_exclusive_group(required=True)
    sources.add_argument("--from-context",type=Path)
    sources.add_argument("--fetch",action="store_true")
    ap.add_argument("--workspace",type=Path)
    ap.add_argument("--compiler",type=Path)
    ap.add_argument("--fetch-timeout-seconds",type=int,default=FETCH_TIMEOUT_SECONDS)
    a=ap.parse_args();need(not os.path.lexists(a.output),"Fresh output required")
    operations=[]
    if a.from_context:
        need(not a.workspace and not a.compiler,"Existing-context validation does not change compiler/workspace")
        c,rows=validate_context(read_json(a.from_context))
        origin=dict(kind="VALIDATED_EXISTING_PINNED_GENERIC_ROOTS",
            context_sha256=sha(a.from_context))
    else:
        need(0<a.fetch_timeout_seconds<=FETCH_TIMEOUT_SECONDS,
            "Fetch timeout must be between 1 and 7200 seconds")
        _fetch_deadline=time.monotonic()+a.fetch_timeout_seconds
        need(a.workspace is not None,"--fetch requires a fresh isolated --workspace")
        workspace=a.workspace.resolve()
        need(not workspace.is_relative_to(REPOSITORY.resolve()),
            "Dependency workspace must be outside the mathematical checkout")
        need(not os.path.lexists(workspace),"Fresh isolated dependency workspace required")
        admission=available_disk(workspace.parent)
        need(admission["free_bytes"]>=FETCH_FREE_DISK_BYTES,
            "Fetch admission requires 32 GiB free disk; this is a planning allowance, not an upper bound")
        compiler=resolve_compiler(a.compiler)
        need(sha(compiler)==COMPILER_SHA256,"Install the exact pinned Linux toolchain or supply --compiler; no toolchain is silently replaced")
        version=command([compiler,"--version"]);need("4.34.0-rc2"in version,"Wrong compiler version")
        workspace.mkdir(parents=True);mathlib=workspace/"mathlib"
        env=fetch_environment(workspace,compiler)
        for key in ["MATHLIB_CACHE_DIR","LAKE_CACHE_DIR","XDG_CONFIG_HOME","CURL_HOME"]:
            Path(env[key]).mkdir(parents=True,exist_ok=True)
        cmds=[
            ["git","clone","--filter=blob:none","--no-checkout","https://github.com/leanprover-community/mathlib4.git",str(mathlib)],
            ["git","-C",str(mathlib),"checkout","--detach",PINS[0][1]],
        ]
        for cmd in cmds:operations.append(dict(command=cmd,stdout=command(cmd,env=env)))
        before=manifest_pins(mathlib)
        lake=compiler.parent/"lake";need(lake.is_file(),"Pinned lake binary absent beside compiler")
        cmd=[str(lake),"exe","cache","get"]
        operations.append(dict(command=cmd,cwd=str(mathlib),stdout=command(cmd,cwd=mathlib,env=env)))
        after=manifest_pins(mathlib)
        need(before==after,"Pinned Mathlib manifest changed while obtaining caches")
        cli_repo=mathlib/".lake/packages/Cli"
        cli_revision=command(["git","-C",cli_repo,"rev-parse","HEAD"],env=env)
        need(cli_revision==CLI_PIN,"Actual build-time Cli revision differs")
        need(not command(["git","-C",cli_repo,"status","--porcelain","--untracked-files=no"],env=env),
            "Actual build-time Cli tracked source is dirty")
        roots=[mathlib/".lake/build/lib/lean"]+[mathlib/".lake/packages"/n/".lake/build/lib/lean"for n,_ in PINS[1:]]
        c,rows=validate_context(dict(compiler=str(compiler),compiler_sha256=COMPILER_SHA256,
            compiler_version=version,generic_lean_path=":".join(map(str,roots)),
            generic_dependencies=DEPENDENCIES),env=env)
        need(time.monotonic()<_fetch_deadline,"Overall fetch deadline expired before acceptance")
        origin=dict(kind="ISOLATED_PINNED_MATHLIB_MANIFEST_AND_OFFICIAL_CACHE",
            workspace=str(workspace),mathlib_manifest_sha256=sha(mathlib/"lake-manifest.json"),
            cache_directory=env["MATHLIB_CACHE_DIR"],xdg_cache_home=env["XDG_CACHE_HOME"],
            lake_cache_directory=env["LAKE_CACHE_DIR"],
            cache_endpoint_overrides_inherited=False,git_credential_prompt_allowed=False,
            credential_environment_variables_not_inherited=list(PUBLIC_FETCH_CREDENTIAL_NAMES),
            fetch_timeout_seconds=a.fetch_timeout_seconds,disk_admission=admission,
            manifest_before_cache=before,manifest_after_cache=after,
            actual_supplemental_build_dependency=dict(name="Cli",revision=cli_revision,
                source_root=str(cli_repo),tracked_source_clean=True,
                included_in_eight_compiled_generic_roots=False))
    c["status"]="PINNED_GENERIC_ARGUMENTS_ONLY_NOT_MATHEMATICAL_PROOF"
    atomic(a.output,c)
    atomic(a.output.with_name(a.output.name+".bootstrap.json"),
        dict(status="PASS_GENERIC_ONLY_CONTEXT_BOOTSTRAP",context_sha256=sha(a.output),
            bootstrap_sha256=sha(Path(__file__)),origin=origin,generic_roots=rows,
            commands=operations,python=sys.version,platform=platform.platform(),
            application_objects_reused=False,mathematical_acceptance=False))
    print(json.dumps(dict(status="PASS_GENERIC_ONLY_CONTEXT_BOOTSTRAP",
        output=str(a.output),context_sha256=sha(a.output),application_objects_reused=False)))
if __name__=="__main__":main()
