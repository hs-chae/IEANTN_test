"""Fixed experiment identity checks. These are metadata checks, never a proof or PV."""
LOCKED_INPUT='9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a'
NUMERATORS={10:1186010558078384875,14:783336421502930946,17:781796015790084776}
SEED17=[999999998851026827562673307794554109,-47936899603066884549003990494659]
TOTAL17=102468342420806369668447945569060309170116
QUAD=12681061983660556400000

def need(value,message):
    if not value:raise ValueError(message)

def validate_scope(candidate):
    need(type(candidate)is dict,'Candidate object required')
    stage=candidate.get('stages')
    need(type(stage)is int and stage in NUMERATORS,'Supported locked stage required')
    need(candidate.get('status')=='UNTRUSTED_EXACT_INTEGER_FOREST_NOT_PROOF_NOT_PV','Candidate status')
    need(type(candidate.get('n'))is int and candidate['n']==2**stage,'Wrong grid')
    need(candidate.get('namespace')=='FapForest'+str(stage),'Wrong numerical scope')
    need(candidate.get('input_sha256')==LOCKED_INPUT,'Wrong original input')
    need(type(candidate.get('norm_numerator'))is int and candidate['norm_numerator']==NUMERATORS[stage],'Wrong recorded numerator')
    need(type(candidate.get('quad'))is int and candidate['quad']==QUAD,'Wrong original curvature sum')
    if stage==17:
        need(candidate.get('seed')==SEED17 and all(type(x)is int for x in candidate['seed']),'Wrong N17 root')
        need(type(candidate.get('total_abs'))is int and candidate['total_abs']==TOTAL17,'Wrong N17 absolute sum')
    expected_payloads={f'w-{s:02}.csv'for s in range(1,stage+1)}|{f'layer-{s:02}.csv'for s in range(1,stage+1)}
    expected_sources={'ForestTables.lean','ForestTablesCheck.lean','ForestFinal.lean'}|{f'ForestData{s:02}.lean'for s in range(1,stage+1)}|{f'ForestCheck{s:02}.lean'for s in range(1,stage+1)}
    for key,expected in [('payloads',expected_payloads),('lean_sources',expected_sources)]:
        rows=candidate.get(key);need(type(rows)is list,'Missing source inventory')
        names=[r.get('file')for r in rows];need(len(names)==len(set(names))and set(names)==expected,'Wrong or duplicate '+key)
