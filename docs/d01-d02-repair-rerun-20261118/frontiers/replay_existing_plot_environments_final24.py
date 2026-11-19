"""Two generic diagnostic plot commands in existing pinned environments only.
No dependency install/download, ANT source program, compiler or model is called.
"""
from collect import O,Path,load,need,sha,pin,save
import argparse,os,subprocess,sys,time,importlib.metadata as metadata

def check(plan):
    for ref in plan['source_pins']:need(sha(ref['path'])==ref['sha256'],'FINAL24_PLOT_SOURCE_DATA_VERSION')
    receipt=load(O/'ACTUAL_ALL24_INTERFACE_NORMAL_O_OO_CONTROLS.json');need(receipt['status']=='PASS_ALL72_ACTUAL_FULL_SOURCE_AND_SEMANTIC_METADATA_CONTROLS'and len(receipt['records'])==72,'ALL72_CURRENT_ACTUAL_SOURCE_INTERFACE_CONTROLS')
    for ref in receipt['input_pins']:need(sha(ref['path'])==ref['sha256'],'ALL72_ACTUALLY_TESTED_CURRENT_SOURCE_INPUTS')
    portable=load(O/'ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json');need(portable['status']=='PASS_TWELVE_ACTUAL_PUBLIC_SOURCE_METADATA_CLIS_NORMAL_O_OO_WITH_ORIGINAL_WORKSPACE_OPEN_DENIAL'and len(portable['records'])==12,'ACTUAL_PUBLIC_SOURCE_ADDRESS_REPRODUCTION')
    for ref in portable['source_pins']:need(sha(ref['path'])==ref['sha256'],'ACTUALLY_TESTED_CURRENT_PORTABLE_SOURCE_VERSION')
    coverage=load(O/'QUANTITATIVE_LITERAL_CLAUSE_COVERAGE.json');need(coverage['status']=='PASS_ALL11411_SOURCE_SCOPE_AND_LITERAL_RECEIVER_COVERAGE','COMPLETE_LITERAL_INTERFACE_SCOPE_BEFORE_FIGURES')
    old=O.parent/'twenty-normalized-frontiers-v1'
    for ref in plan['installed_environment_manifests']:
        file=Path(ref['path']);need(sha(file)==ref['sha256'],'ACTUAL_COLD_VERIFIED_INSTALL_MANIFEST');manifest=load(file);root=Path(manifest['root']);need(root in [old/'plot-dependencies',old/'plot-regeneration-dependencies'],'ONLY_TWO_RETAINED_EXISTING_ENVIRONMENTS');need(root.is_dir()and not root.is_symlink(),'ACTUAL_EXISTING_ORDINARY_INSTALLED_ROOT')
        files=[p for p in root.rglob('*')if p.is_file()or p.is_symlink()];need(not any(p.is_symlink()for p in files),'NO_INSTALLED_EXTERNAL_SYMLINK');need({str(p.relative_to(root))for p in files}=={x['path']for x in manifest['files']},'FULL_INSTALLED_PHYSICAL_MEMBERSHIP')
        for row in manifest['files']:
            p=root/row['path'];need(p.stat().st_size==row['bytes']and sha(p)==row['sha256'],'EACH_EXISTING_INSTALLED_SOURCE_BYTE')
        distributions=sorted([{'name':d.metadata['Name'],'version':d.version}for d in metadata.distributions(path=[str(root)])],key=lambda x:x['name'].lower());need(distributions==manifest['installed_distributions']and len(distributions)==11,'EXACT_EXISTING_11_WHEEL_VERSION_SET')
    return receipt

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--check',action='store_true');ap.add_argument('--execute',action='store_true');ap.add_argument('--approval',type=Path);ap.add_argument('--approval-sha256');a=ap.parse_args();need(a.check!=a.execute,'EXACTLY_ONE_METADATA_CHECK_OR_EXPLICIT_EXECUTION')
    path=O/'PLOT_EXECUTION_PLAN_FINAL24_UNSIGNED.json';plan=load(path);check(plan)
    if a.check:print('PASS_FINAL24_METADATA_ONLY_COMPLETE_SOURCE_SCOPE_72CONTROLS_2PINNED_ENVIRONMENTS_NO_PLOT_EXECUTION');return
    need(a.approval is not None and a.approval_sha256 is not None and sha(a.approval)==a.approval_sha256,'EXACT_ROOT_PLOT_EXECUTION_AUTHORITY');approval=load(a.approval);need(approval.get('reviewed_by')=='/root'and approval.get('plan',{}).get('sha256')==sha(path),'ROOT_AUTHORITY_EXACT_FINAL24_PLAN')
    out=O/plan['execution_receipt'];need(not out.exists(),'FRESH_OWNED_FINAL24_PLOT_RECEIPT');record={'status':'RUNNING_ROOT_APPROVED_FINAL24_DIAGNOSTIC_PLOTS','authority':pin(a.approval),'plan':pin(path),'source':pin(__file__),'commands':[],'new_ANT_mathematical_verification':False,'full_operator_optimization':False,'fresh_dependency_installs':0};save(out.name,record);first=None
    for command in plan['commands']:
        start=time.monotonic();result=subprocess.run(command['argv'],cwd=O,env=dict(os.environ,**command['environment']),capture_output=True,text=True);record['commands'].append({**command,'cwd':str(O),'exit_code':result.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':result.stdout,'stderr':result.stderr});save(out.name,record);need(result.returncode==0,'FINAL24_PLOT_COMMAND_FAILED_PARTIAL_RETAINED');outputs={name:sha(O/name)for name in plan['outputs']}
        if first is None:first=outputs
        else:need(first==outputs,'ALL_THREE_SVGS_AND_FULL_SOURCE_LINEAGE_CSV_BYTE_IDENTICAL')
        check(plan)
    record.update(status='PASS_FINAL24_TWO_EXISTING_COLD_VERIFIED_ENVIRONMENTS_BYTE_IDENTICAL_DIAGNOSTIC_PLOTS',outputs=first);save(out.name,record);print(record['status'])
if __name__=='__main__':main()
