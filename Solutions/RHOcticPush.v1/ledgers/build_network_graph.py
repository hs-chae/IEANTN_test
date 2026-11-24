#!/usr/bin/env python3
"""Census every canonical metadata node; do not confuse metadata with proof use.

The small rendered path is selected explicitly from the complete census. Each
drawn edge must occur in actual conclusion imports. Compiler/body audits remain
separate evidence; this script accepts no mathematical theorem or PV claim.
"""
import argparse
import datetime
import hashlib
import html
import json
import re
import subprocess
from pathlib import Path
import yaml

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASELINE = '0e2638852a08de84e25f1d179a36356fb12333a5'


class UniqueLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node, deep=False):
    result = {}
    for key, value in node.value:
        k = loader.construct_object(key, deep=deep)
        if k in result:
            raise ValueError('Duplicate YAML key: ' + str(k))
        result[k] = loader.construct_object(value, deep=deep)
    return result


UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def build():
    paths = sorted((REPO/'IEANTN/Nodes').rglob('formalization.yaml'))
    nodes, conclusions, edges, source_pins = {}, {}, [], []
    for p in paths:
        data = p.read_bytes()
        relative = p.relative_to(REPO).as_posix()
        m = yaml.load(data, Loader=UniqueLoader)
        node = m['node']['id']
        if node in nodes:
            raise ValueError('Duplicate node identity: ' + node)
        old = subprocess.run(['git','show',BASELINE+':'+relative],capture_output=True)
        if old.returncode == 0 and old.stdout != data:
            raise ValueError('Existing baseline metadata changed: ' + relative)
        partition = 'unchanged_preexisting' if old.returncode == 0 else 'this_campaign_added'
        conclusion_source = p.with_name('Conclusions.lean')
        text = conclusion_source.read_bytes()
        old_conclusions = subprocess.run(
            ['git','show',BASELINE+':'+str(conclusion_source.relative_to(REPO))],
            capture_output=True)
        if old_conclusions.returncode == 0 and old_conclusions.stdout != text:
            raise ValueError('Existing baseline mathematical statements changed: '+relative)
        source_pins.extend([dict(path=relative,sha256=sha(data)),
            dict(path=conclusion_source.relative_to(REPO).as_posix(),sha256=sha(text))])
        nodes[node] = dict(id=node,metadata=relative,sha256=sha(data),partition=partition,
            recorded_status=m['node'].get('status'),kind=m['node'].get('kind'),
            sources=m.get('sources',[]),
            source_provenance_status='Not established by this metadata census')
        for c in m.get('conclusions',[]):
            key = node + '.' + c['id']
            if key in conclusions:
                raise ValueError('Duplicate conclusion identity: ' + key)
            declaration = c['declaration']
            short = declaration.rsplit('.',1)[-1]
            pattern = re.compile(r'^\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+'
                                 + re.escape(short) + r'(?:\s|\(|\{|:|$)')
            candidates = [i for i,line in enumerate(text.decode().split('\n'),1)
                          if pattern.match(line)]
            if len(candidates) != 1:
                raise ValueError('Ambiguous written conclusion identity: '+key)
            conclusions[key] = dict(id=key,node=node,declaration=declaration,
                file=conclusion_source.relative_to(REPO).as_posix(),
                physical_LF_line=candidates[0] if len(candidates)==1 else None,
                line_candidates=candidates,source_sha256=sha(text),
                recorded_import_status=c.get('imports_status'),
                recorded_justifications=c.get('justifications',[]),
                proof_status='Not established by this metadata census')
            for dependency in c.get('imports',[]):
                edges.append(dict(source=dependency['node']+'.'+dependency['conclusion'],
                                  target=key,kind='declared_metadata_import'))
    unresolved = [e for e in edges if e['source'] not in conclusions]
    if unresolved:
        raise ValueError('Unresolved canonical metadata edges')
    for pin in source_pins:
        if sha((REPO/pin['path']).read_bytes()) != pin['sha256']:
            raise ValueError('Concurrent source change: ' + pin['path'])
    if paths != sorted((REPO/'IEANTN/Nodes').rglob('formalization.yaml')):
        raise ValueError('Canonical metadata universe changed during census')
    return dict(status='COMPLETE_CANONICAL_METADATA_CENSUS_NOT_FULL_PROOF_OR_SOURCE_AUDIT',
        baseline_commit=BASELINE,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        selection='Every formalization.yaml recursively below the current IEANTN/Nodes tree; '
                  'no source-facing heuristic or old sorry ledger used',
        yaml_version=yaml.__version__,node_count=len(nodes),conclusion_count=len(conclusions),
        edge_count=len(edges),added_nodes=sum(n['partition']=='this_campaign_added' for n in nodes.values()),
        unresolved_metadata_edges=unresolved,nodes=list(nodes.values()),
        conclusions=list(conclusions.values()),edges=edges,source_pins=source_pins)


def focus_svg(graph, custom_rows=None, key='ramanujan'):
    # This display selection was made by the research coordinator. The full
    # requested canonical graph remains in the JSON, including every exclusion.
    rows = [
        ('RH.v1.hypothesis','RH',0,0),
        ('IntegratedPerron.v1.formula','General Perron formula',0,80),
        ('Nicolas.v1.spectral_bound','Nicolas zero information',0,160),
        ('RHPrimeCounting.v5.compensation_profile','Signed compensation profile',270,80),
        ('Buthe.v1.table_1_interval_bounds','Finite Chebyshev table',0,280),
        ('Buthe.v1.theorem_2_li_minus_pi','Lower Li gap bound',0,360),
        ('Buthe.v1.theorem_2_li_gt_pi','Upper Li gap bound',0,440),
        ('RamanujanGap.v6.local_606b','606–610 billion margin',540,280),
        ('RamanujanGap.v5.full_profile','Retained stronger profile',270,540),
        ('RamanujanGap.v6.full_profile','Retained whole-ray profile',810,280),
        ('RamanujanGap.v6.margin_606b','Margin from 606 billion',1080,280),
        ('RamanujanGap.v6.ramanujan','Strict Ramanujan inequality',1080,440)]
    if custom_rows is not None:
        rows = custom_rows
    indexed = {c['id']:c for c in graph['conclusions']}
    if any(k not in indexed for k,_,_,_ in rows):
        raise ValueError('Missing actual focus conclusion')
    positions = {k:(x+15,y+15) for k,_,x,y in rows}
    parts = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1350 650" '
             'role="img" aria-label="Actual declared typed network dependencies">',
             '<defs><marker id="graph-arrow-'+key+'" markerWidth="8" markerHeight="8" refX="7" '
             'refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#53708d"/></marker></defs>']
    shown = []
    for edge in graph['edges']:
        if edge['source'] not in positions or edge['target'] not in positions:
            continue
        x,y = positions[edge['source']];a,b = positions[edge['target']]
        parts.append(f'<path d="M{x+230},{y+28} C{x+260},{y+28} {a-30},{b+28} {a},{b+28}" '
                     'fill="none" stroke="#53708d" stroke-width="2" marker-end="url(#graph-arrow-'+key+')"/>')
        shown.append(edge)
    for key,label,x,y in rows:
        x+=15;y+=15;c=indexed[key]
        parts.append(f'<g><title>{html.escape(key)}</title><rect x="{x}" y="{y}" width="230" '
                     'height="58" rx="7" fill="#eef4fb" stroke="#6c91bb"/>'
                     f'<text x="{x+10}" y="{y+23}" font-family="system-ui,sans-serif" font-size="14">'
                     f'{html.escape(label)}</text><text x="{x+10}" y="{y+43}" '
                     'font-family="monospace" font-size="10">'+html.escape(key)+'</text></g>')
    parts.append('</svg>')
    return ''.join(parts),dict(selection_author='Research coordinator',
        inclusion='Exactly '+str(len(rows))+' named conclusions on the '+key+' path',
        exclusion='All other canonical conclusions are omitted only from this small display, not the JSON census',
        selected_conclusions=[r[0] for r in rows],selected_edges=shown,
        actual_compiled_consumption_evidence='Separate canonical source/body/axiom audit receipts; '
            'metadata edges alone do not establish theorem consumption')


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    if a.out.exists():raise ValueError('Use a fresh graph output directory')
    graph=build();svg,selection=focus_svg(graph);a.out.mkdir(parents=True)
    (a.out/'NETWORK_GRAPH.json').write_text(json.dumps(graph,indent=2,ensure_ascii=False)+'\n')
    (a.out/'NETWORK_FOCUS.svg').write_text(svg)
    (a.out/'DISPLAY_SELECTION.json').write_text(json.dumps(selection,indent=2,ensure_ascii=False)+'\n')
    feedback_rows = [
        ('RH.v1.hypothesis','RH',0,0),
        ('IntegratedPerron.v1.formula','General Perron formula',0,80),
        ('Nicolas.v1.spectral_bound','Nicolas zero information',0,160),
        ('BPTOffOrdinate.v1.bound','BPT zero count',0,240),
        ('RHPrimeCounting.v5.compensation_profile','Signed compensation profile',270,0),
        ('RHPrimeCounting.v6.J_upper','J upper bound before pi error',270,240),
        ('RHPrimeCounting.v6.prime_power_feedback','Prime-square correction',540,240),
        ('RHPrimeCounting.v6.ordinary_transfer','Full ordinary-pi transfer',810,80),
        ('RHSmoothing.v3.box_psi','Actual Box psi bound',540,0),
        ('RHPrimeCounting.v6.box_Li','Effective ordinary-pi bound',810,280),
        ('RHPrimeCounting.v6.box_interval','Actual interval count',1080,200),
        ('RHPrimeCounting.v6.clean_pi','Clean21/50 corollary',1080,360)]
    svg,selection=focus_svg(graph,feedback_rows,'prime-square-feedback')
    (a.out/'NETWORK_FEEDBACK.svg').write_text(svg)
    (a.out/'FEEDBACK_SELECTION.json').write_text(json.dumps(selection,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:graph[k] for k in ['status','node_count','conclusion_count','edge_count','added_nodes']}))


if __name__=='__main__':main()
