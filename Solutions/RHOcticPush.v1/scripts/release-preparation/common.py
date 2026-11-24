"""Strict artifact helpers; none of these checks establish mathematical truth."""
import hashlib
import json
import math
import os
import re
import stat
from pathlib import Path, PurePosixPath


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(8 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    def unique(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key: '+key)
            result[key] = value
        return result
    def finite(value):
        result = float(value)
        need(math.isfinite(result), 'nonfinite JSON number')
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique,
        parse_float=finite,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def relative(value):
    need(type(value) is str and value != '', 'explicit relative path required')
    path = PurePosixPath(value)
    need(not path.is_absolute() and '..' not in path.parts and str(path) == value
         and '\\' not in value, 'canonical relative path required: '+value)
    return value


def identity(path):
    path = Path(path)
    need(stat.S_ISREG(path.lstat().st_mode), 'regular nonsymlink file required: '+str(path))
    return dict(bytes=path.stat().st_size, sha256=sha(path))


def checked(path, row):
    got = identity(path)
    need(type(row['bytes']) is int and row['bytes'] == got['bytes'] and
         type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}', row['sha256'])
         and row['sha256'] == got['sha256'], 'pinned artifact differs: '+str(path))
    return got


def save(path, value):
    path = Path(path)
    need(not os.path.lexists(path), 'fresh output required: '+str(path))
    temporary = path.with_name('.'+path.name+'.pending')
    need(not os.path.lexists(temporary), 'fresh atomic temporary required')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False)+'\n')
    try:
        os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)
