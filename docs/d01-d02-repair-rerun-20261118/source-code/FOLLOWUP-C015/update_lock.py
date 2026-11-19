#!/usr/bin/python3.10
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
x=[{"path":f.name,"sha256":hashlib.sha256(f.read_bytes()).hexdigest()} for f in sorted(p.iterdir()) if f.is_file() and f.name!="LOCK.json"]
(p/"LOCK.json").write_text(json.dumps({"files":x},indent=2)+"\n")
