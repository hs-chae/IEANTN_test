#!/usr/bin/env python3
"""Portable immutable source-only contract; never theorem acceptance or source-first PV."""
import hashlib,json,math,os,re,tempfile
from pathlib import Path
PACKAGE=Path(__file__).resolve().parents[1]
LOCKED_SHA = {13: '1531abe7a1b66a478433fe6c73236db02be2d2a600cb954c121ad771ee33312d', 24: 'a00478c770029975ff1ba79abd22ff7b91bd5cb3227ac421ec5026ea6e33b588'}
TOOL_IDS_SHA = '1af40d760e085643ceb173010e2376ee74a1b6377aab6a79293632e9a7b3b499'

FOUNDATION_SHA = {13: 'd0794d6f0aad7a7c572183a9c39ac1056fcbc79c344c408d6d1810db22dd8da2', 24: 'ee965fff1f8f58532e6b4d4b6a0d65749bb1fcfbc89a60a9fe11b2bd5cfdb819'}
HELPERS={'TopShapeSymbolic.lean':'121b1b44651f312abf569164f5117fe33ffb18d5ab3fc4f1c6f564fafee56726',
         'NormSymbolic.lean':'dc3590afbf7a804cc8d033db03dbdda826f4575f6d2f59755a9c97d43500b333'}
FINAL={13:'f9385eea472ff94103487ac94b64fe02dab5c354da6ace5b591bacdc323ad416',
       24:'edd68a4f35cb9c5bc34385630683145c3782f8516d8ee87ab3b2fac42488667e'}
AUDIT={13:'e8b3eca548be6a43769f50744859e388fff2276eadb1d537836ac34d1be23a65',
       24:'d950c97f4f95f8282a76f35baa435796aa8d09f282195efc0877221768829f67'}
GENERATOR_SHA='e04d714e7cc0d09c9d399cec36be2c007649bd07a3db1c9b3af4296480165fd2'


def need(value,message):
    if not value:raise ValueError(message)


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as stream:
        for block in iter(lambda:stream.read(8*2**20),b''):h.update(block)
    return h.hexdigest()


def load(path):
    def pairs(items):
        result={}
        for k,v in items:
            need(k not in result,'Duplicate JSON key '+k);result[k]=v
        return result
    def bad(v):raise ValueError('Nonfinite JSON '+v)
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=bad)


def publish(path,value):
    need(not os.path.lexists(path),'Fresh receipt required')
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=path.parent)
    try:
        with os.fdopen(fd,'w')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,path)
    finally:Path(tmp).unlink()


def imports(path):
    return [n for line in Path(path).read_text().splitlines()if line.startswith('import ')
            for n in line[7:].split('--',1)[0].split()]


def locked(stage):
    need(type(stage)is int and stage in[13,24],'Only original S13/N24 supported')
    path=PACKAGE/'locked'/f'original-candidate-{stage}.json'
    need(sha(path)==LOCKED_SHA[stage],'Locked original numerical inventory changed')
    value=load(path)
    for name,digest in HELPERS.items():need(sha(PACKAGE/'helpers'/name)==digest,'Pinned mathematical helper changed')
    need(sha(PACKAGE/'tools/generate_compact_final_v2.py')==GENERATOR_SHA,'Executed source generator changed')
    need(sha(PACKAGE/'locked'/f'W4D{stage}ClaimAudit.lean')==AUDIT[stage],'Original typed audit template changed')
    return value


def check_foundations(project,stage):
    path=PACKAGE/'locked'/f'original-foundations-{stage}.json'
    need(sha(path)==FOUNDATION_SHA[stage],'Locked mathematical foundation inventory changed')
    rows=load(path)['source_rows']
    need(len(rows)==12,'Original mathematical foundation scope changed')
    for row in rows:
        source=project/row['project_relative_source']
        need(sha(source)==row['sha256']and imports(source)==row['imports'],'Original mathematical execution specification/data foundation changed: '+row['module'])
    return rows


def check_project(project):
    path=PACKAGE/'locked/original-tool-identities.json';need(sha(path)==TOOL_IDS_SHA,'Original tool identity table changed')
    identities=load(path)
    for value in identities.values():need(sha(project/value['path'])==value['sha256'],'Original checker/producer/platform tool changed: '+value['path'])
    return identities


def check_original_schema(proposal,expected):
    fixed=set(expected)-{'modules','payloads','original_producer_plan_sha256'}
    need(set(proposal)==fixed|{'modules','payloads','source_input','producer_seconds'},'Original producer PLAN schema changed')
    for k in fixed:need(proposal[k]==expected[k],'Original numeric algorithm/parameter/claim changed: '+k)
    need(proposal['modules']==expected['modules'],'Original numeric source hashes/imports/bytes changed')
    need(proposal['payloads']==expected['payloads'],'Original937/91 literal input hashes/bytes changed')
    elapsed=proposal['producer_seconds'];need(type(elapsed)in[int,float]and math.isfinite(elapsed)and elapsed>=0,'Invalid producer timing')
    need(type(proposal['source_input'])is str and proposal['source_input'],'Missing original input provenance')


def check_numeric_files(root,proposal,original_final=None):
    final=proposal['final_module']+'.lean'
    for row in proposal['modules']:
        name=row['file'];need(Path(name).name==name and name.endswith('.lean'),'Invalid source filename')
        source=original_final if name==final and original_final is not None else root/name
        need(source.is_file()and source.stat().st_size==row['bytes']and sha(source)==row['sha256'],'Original generated numeric source changed: '+name)
        need(imports(source)==row['imports'],'Original generated numeric imports changed')
    for row in proposal['payloads']:
        name=row['file'];need(Path(name).name==name and name.endswith('.csv'),'Invalid data filename')
        source=root/name;need(source.is_file()and source.stat().st_size==row['bytes']and sha(source)==row['sha256'],'Original literal numerical input changed: '+name)


def validate_original(candidate,project,input_path=None):
    check_project(project);proposal=load(candidate/'PLAN.json');expected=locked(proposal['stages']);check_foundations(project,proposal['stages']);check_original_schema(proposal,expected);check_numeric_files(candidate,proposal)
    input_path=Path(input_path)if input_path is not None else Path(proposal['source_input'])
    need(input_path.is_file()and sha(input_path)==proposal['input_sha256'],'Actual original mathematical input missing/changed; supply --input')
    return proposal


def expected_derived_modules(original):
    stage=original['stages'];result=[]
    for row in original['modules']:
        if row['file']==original['final_module']+'.lean':
            path=PACKAGE/'locked'/f'accepted-W4D{stage}Final.lean'
            need(sha(path)==FINAL[stage],'Accepted same-statement Final source changed')
            result.append(dict(file=row['file'],imports=imports(path),sha256=FINAL[stage],bytes=path.stat().st_size))
        else:result.append(row)
    for name,digest in HELPERS.items():
        path=PACKAGE/'helpers'/name;result.append(dict(file=name,imports=imports(path),sha256=digest,bytes=path.stat().st_size))
    return result


def validate_derived(candidate,project):
    check_project(project);proposal=load(candidate/'PLAN.json');stage=proposal['stages'];expected=locked(stage);check_foundations(project,stage)
    original=load(candidate/'ORIGINAL_PRODUCER_PLAN.json');check_original_schema(original,expected)
    metadata=proposal.get('compact_proof_repair');need(type(metadata)is dict and metadata['kind']=='SOURCE_ONLY_TWO_PROOF_BODIES_SAME_PUBLIC_TYPES','Wrong proof-only transformation kind')
    need(metadata['original_plan_sha256']==sha(candidate/'ORIGINAL_PRODUCER_PLAN.json')and metadata['generator_sha256']==GENERATOR_SHA,'Original/generated source association differs')
    need(metadata['original_namespace_and_final_module_preserved']is True and metadata['untrusted_proposal_not_proof_not_PV']is True,'Wrong verification tier')
    compare=dict(proposal);compare.pop('compact_proof_repair');compare['modules']=original['modules']
    need(compare==original,'A mathematical parameter/input/algorithm/claim besides proof source changed')
    need(proposal['modules']==expected_derived_modules(original),'Derived source inventory changed beyond exact two helpers/Final')
    check_numeric_files(candidate,original,candidate/'original'/f'W4D{stage}Final.lean')
    for row in proposal['modules']:
        p=candidate/row['file'];need(p.stat().st_size==row['bytes']and sha(p)==row['sha256']and imports(p)==row['imports'],'Derived source differs')
    need(not any('ImportsProbe'in row['file']or'ClaimAudit'in row['file']for row in proposal['modules']),'Diagnostic/candidate-owned audit injected into mathematical inventory')
    receipt=load(candidate/'PROOF_TRANSFORM_RECEIPT.json')
    need(receipt['status']=='PASS_SOURCE_ONLY_TRANSFORM_NOT_PROOF_NOT_PV'and receipt['derived_plan_sha256']==sha(candidate/'PLAN.json'),'Missing exact source-only transformation receipt')
    need(receipt['same_public_headers']==stage+7 and receipt['changed_public_bodies']==['top_shape','numerator_checked'],'Original mathematical source identities differ')
    need(receipt['original_ClaimAudit_sha256']==AUDIT[stage]and receipt['original_numeric_sources_unchanged']==len(original['modules'])-1 and receipt['original_payloads_unchanged']==len(original['payloads']),'Original source/data/typed audit coverage differs')
    return dict(proposal=proposal,original=original,receipt=receipt)
