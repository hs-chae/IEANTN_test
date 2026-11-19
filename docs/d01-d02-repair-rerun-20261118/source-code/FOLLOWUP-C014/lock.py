import pathlib,json,hashlib
w=pathlib.Path(__file__).parent
(w/'LOCK.json').write_text(json.dumps({'files':[{'path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(w.iterdir()) if p.is_file() and p.name!='LOCK.json']})+'\n')
