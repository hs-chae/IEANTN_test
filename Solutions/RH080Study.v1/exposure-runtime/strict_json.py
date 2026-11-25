"""Optimization-independent strict parsing for additive runtime metadata."""
import json


def read(path):
    def pairs(items):
        out={}
        for key,value in items:
            if key in out:raise ValueError('Duplicate JSON key')
            out[key]=value
        return out
    def nonfinite(value):
        raise ValueError('Non-finite JSON constant: '+value)
    return json.loads(path.read_bytes(),object_pairs_hook=pairs,parse_constant=nonfinite)
