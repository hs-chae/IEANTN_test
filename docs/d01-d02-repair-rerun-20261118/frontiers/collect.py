"""Lossless collection of the twenty-four explicitly sealed portfolios, no ANT execution."""
from pathlib import Path
import collections,hashlib,json,math
from source_resolver import read_bytes,source_is_file,physical_relative_files,MAP,ORIGINAL_STUDY
N=ORIGINAL_STUDY if MAP is not None else Path(__file__).resolve().parents[2]; O=Path(__file__).resolve().parent
EXPECTED={1:770,2:199,3:436,4:124,5:155,6:182,7:1923,8:401,9:1002,10:220,11:213,12:297,13:297,14:436,15:346,16:196,17:921,18:241,19:644,20:294,21:247,22:1005,23:483,24:379}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def load(p):
    def pairs(a):
        d={}
        for k,v in a:
            need(k not in d,'duplicate JSON key '+k); d[k]=v
        return d
    def bad(x): raise ValueError('nonfinite JSON '+x)
    def finite(s):
        v=float(s);need(math.isfinite(v),'nonfinite JSON float');return v
    return json.loads(read_bytes(p),object_pairs_hook=pairs,parse_constant=bad,parse_float=finite)
def sha(p):return hashlib.sha256(read_bytes(p)).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
def verified(r):
    p=Path(r['path']);need(sha(p)==r['sha256'],'source pin mismatch '+str(p));return p
def save(n,x):
    p=O/n;t=p.with_suffix('.tmp');t.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n');t.replace(p)
def validate_lock(p):
    j=load(p); fs=j['files']; need(len(fs)==len({x['path'] for x in fs}),'duplicate LOCK path')
    for x in fs:need(sha(p.parent/x['path'])==x['sha256'],'locked payload changed '+str(p.parent/x['path']))
    physical=physical_relative_files(p.parent)
    need(physical=={x['path'] for x in fs}|{'LOCK.json'},'physical LOCK membership '+str(p))
    return fs
def main():
    selection=load(O/'FROZEN_FINALIZATION_SELECTION.json');old=selection['canonical_coordinates']
    wanted={f'FOLLOWUP-C{i:03}':n for i,n in EXPECTED.items()}
    finals=[(verified(ref),load(verified(ref)))for ref in selection['finalizations']]
    need(len(finals)==len(wanted)==len({f['candidate_id'] for p,f in finals}),'exact sealed stage set')
    objects=[]; portfolios=[]
    for fp,f in sorted(finals,key=lambda a:a[1]['candidate_id']):
        cid=f['candidate_id']; need(f['reviewed_by']=='/root','Root seal required')
        need(f.get('remaining_substantive_mathematical_gaps',f.get('remaining_current_D01_mathematical_gaps',[]))==[],'finalization gaps')
        sr=next(v for k,v in f.items() if k.startswith('complete') and 'source'in k and isinstance(v,dict)and'path'in v)
        mr=next(v for k,v in f.items() if 'independent_M_review'in k and isinstance(v,dict)and'path'in v)
        fr=next(v for k,v in f.items() if 'floor'in k and isinstance(v,dict)and'path'in v and 'full_validated'in k)
        sp=verified(sr);mp=verified(mr);floor=load(verified(fr));sf=validate_lock(sp);mf=validate_lock(mp)
        raw=load(mp.parent/'review.json');byid={x['claim_id']:x for x in raw['claims']};need(len(byid)==len(raw['claims']),'unique raw claim IDs')
        floorrows_list=floor.get('claims',floor.get('complete_current_active_claims',[]))
        ids=floor.get('validated_claim_ids_by_family',floor.get('claim_ids_by_family'))
        if ids is None and 'validated_D01_portfolio'in floor:
            ids={q['family']:q['claim_ids']for q in floor['validated_D01_portfolio']}
        if ids is None:ids={fam:[q['claim_id']for q in floorrows_list if q['family']==fam]for fam in ['Ramanujan','Mertens']}
        active={i for a in ids.values() for i in a};need(len(active)==wanted[cid] and active<=byid.keys(),'exact active universe '+cid)
        roots=[sp.parent];views=[]
        assoc=load(verified(f['complete_Root_assessment']))
        if 'reviewed_source_view_manifest'in assoc:
            vp=verified(assoc['reviewed_source_view_manifest']);validate_lock(vp);roots.append(vp.parent);views.append(assoc['reviewed_source_view_manifest'])
        for k,v in f.items():
            if 'view'in k and isinstance(v,dict)and'path'in v:
                vp=verified(v);validate_lock(vp);roots.append(vp.parent);views.append(v)
        if cid=='FOLLOWUP-C021':
            vp=N/'protocol/own-history-common-M-review-preparation-v1/FOLLOWUP-C021/SOURCE_PRESERVING_OWN_HISTORY_VIEW_UNSIGNED/LOCK.json'
            need(sha(vp)=='35ac995ae37dd258a1d3bac3ab4f7cb8c46996b7076360e297fa28ac635b54b1','C021 closed view');validate_lock(vp);roots.append(vp.parent);views.append(pin(vp))
        hashfiles=collections.defaultdict(list)
        for rt in roots:
            for x in load(rt/'LOCK.json')['files']:hashfiles[x['sha256']].append(rt/x['path'])
        rows_by_id={}
        floorrows={x['claim_id']:x for x in floorrows_list if isinstance(x,dict)and'claim_id'in x}
        for fam in ['Ramanujan','Mertens']:
            for ident in ids[fam]:
                rawrow=byid[ident];need(rawrow['family']==fam,'exact family')
                if ident in rows_by_id:
                    r=rows_by_id[ident];p=Path(r['source']['file']);need(sha(p)==r['source']['sha256'],'old exact written source')
                else:
                    ref=rawrow['written_source'];digest=ref['sha256'];names=[ref.get(k) for k in ['original_name','restored_name','original_file','original_basename','file'] if ref.get(k)]
                    choices=[]
                    for rt in roots:
                        for name in names:
                            q=Path(name) if Path(name).is_absolute() else rt/name
                            if source_is_file(q)and sha(q)==digest:choices.append(q)
                    if not choices:choices=hashfiles[digest]
                    need(bool(choices),'unresolved source '+cid+' '+ident);p=choices[0]
                    lf=ref['physical_LF'];ls=read_bytes(p).decode().split('\n')
                    end=next((ref[k] for k in ['physical_LF_end_inclusive','physical_LF_end','last_physical_LF','end_physical_LF','physical_LF_last','through_physical_LF'] if k in ref),lf)
                    need(type(lf)is int and type(end)is int and 1<=lf<=end<=len(ls),'byte-LF identity')
                    r={'key':[cid,ident],'candidate_id':cid,'stage_id':f['stage_id'],'family':fam,'claim_id':ident,
                       'source':{'file':str(p),'physical_LF':lf,'physical_LF_end':end,'sha256':digest,'packet_source':ref,'exact_written_readback':'\n'.join(ls[lf-1:end])},
                       'raw_M_row':rawrow,'raw_M_row_sha256':hashlib.sha256(json.dumps(rawrow,sort_keys=True,ensure_ascii=False).encode()).hexdigest()}
                r.update(Root_finalization=pin(fp),Root_floor=fr,Root_object_qualification=floorrows.get(ident),retained_without_selection=True)
                objects.append(r)
        portfolios.append({'candidate_id':cid,'stage_id':f['stage_id'],'Root_finalization':pin(fp),'complete_source':sr,'complete_fresh_M':mr,
            'raw_review':pin(mp.parent/'review.json'),'Root_floor':fr,'Root_statement':f,'all_valid_object_ids_by_family':ids,
            'all_valid_objects':len(active),'all_raw_review_objects':len(byid),'inactive_raw_objects':[x for x in raw['claims'] if x['claim_id']not in active],
            'candidate_payloads':len(sf),'review_payloads':len(mf),'review_source_views':views})
    need(len(objects)==sum(EXPECTED.values())==len({tuple(r['key']) for r in objects}),'full unique scope')
    save('ALL24_SOURCE_BOUND_OBJECTS.json',{'schema':'TWENTYFOUR_FINALIZED_LOSSLESS_FRONTIER_SOURCE_UNIVERSE_V1','portfolios':portfolios,'objects':objects,
        'all_active_scoped_objects':len(objects),'canonical_R':old['canonical_R'],'canonical_M':old['canonical_M'],
        'scope':'Exactly all24 named Root-finalized canonical stages, with current explicit mathematical qualifications. Repaired versions replace historical versions for active mathematics, never primary experimental outcomes.',
        'coverage_rule':'All IDs in every exact Root-sealed full floor, with all raw inactive rows retained separately. No formula parser or heuristic selects the assertion universe.',
        'trust':'Existing written mathematics, original literature and ordinary numerical execution; no full analytic Lean or source-first PV; data conversion creates no new mathematical proof.'})
    print(json.dumps({'status':'PASS_ALL24_LOSSLESS_SOURCE_COLLECTION','objects':len(objects),'portfolios':[(p['candidate_id'],p['all_valid_objects']) for p in portfolios]}))
if __name__=='__main__':main()
