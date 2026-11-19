"""Narrow source-bound supplementary coordinates for reviewed literal clauses.

This serializes existing accepted written statements. It does not execute any
mathematical source program, prove its arithmetic, or establish source-first PV.
"""
from collect import O,load,need,sha
from functools import lru_cache
import copy
@lru_cache(None)
def entries():
    out={}
    for name in ['REVIEWED_M_LITERAL_RECEIVER_INTERFACES_V1.json','REVIEWED_R_LITERAL_RECEIVER_INTERFACES_V1.json']:
        p=O/name
        need(p.is_file(),'REQUIRED_LITERAL_INTERFACE_TABLE_MISSING '+name)
        table=load(p);need(table['schema']=='SOURCE_REVIEWED_LITERAL_RECEIVER_INTERFACE_SUPPLEMENT_V1','LITERAL_INTERFACE_TABLE_SCHEMA');need(table['source_universe']['sha256']==sha(O/'ALL24_SOURCE_BOUND_OBJECTS.json'),'LITERAL_INTERFACE_EXACT_SOURCE_SNAPSHOT')
        for row in table['entries']:
            key=tuple(row['key']);need(key not in out,'UNIQUE_LITERAL_INTERFACE_SOURCE_KEY');out[key]=row
    return out

def lookup(row):
    entry=entries().get(tuple(row['key']))
    if entry is None:return None
    source={k:row['source'][k]for k in ['file','sha256','physical_LF','physical_LF_end']};raw=row['raw_M_row'];need(source==entry['exact_written_source'],'LITERAL_INTERFACE_WRITTEN_FILE_SHA_LF');need(raw['exact_statement']==entry['exact_statement']and raw['full_domain']==entry['exact_domain']and raw['assumptions']==entry['exact_assumptions'],'LITERAL_INTERFACE_EXACT_STATEMENT_DOMAIN_PREMISES')
    need(entry['reviewed_clause_role']in ['FINITE_EXPLICIT_BOUND_FUNCTION','COMPOUND_VALID_BOUND_AND_DIAGNOSTIC'],'LITERAL_INTERFACE_POSITIVE_CLAUSE_ROLE')
    return entry

def bounds(row):
    entry=lookup(row);return None if entry is None else copy.deepcopy(entry['functions'])
