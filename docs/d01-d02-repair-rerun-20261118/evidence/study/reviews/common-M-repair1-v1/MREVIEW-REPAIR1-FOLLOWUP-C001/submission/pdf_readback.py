from pathlib import Path
import re,zlib,hashlib
def objects(src):
    d={int(m[1]):m[2] for m in re.finditer(rb'(?:^|[\r\n])(\d+) 0 obj\s*(.*?)\s*endobj',src,re.S)}
    for v in list(d.values()):
        if b'/ObjStm' not in v.split(b'stream',1)[0]:continue
        pre,b=v.split(b'stream',1)
        b=zlib.decompress(b.lstrip(b'\r\n'))
        first=int(re.search(rb'/First\s+(\d+)',pre)[1])
        tab=list(map(int,b[:first].split()))
        pairs=list(zip(tab[::2],tab[1::2]))
        for (n,off),(_,end) in zip(pairs,pairs[1:]+[(0,len(b)-first)]):
            d[n]=b[first+off:first+end].strip()
    return d
def streams(d, pg):
    c=re.search(rb'/Contents\s*(\[[^\]]+\]|\d+ 0 R)',d[pg])[1]
    for sn in map(int,re.findall(rb'(\d+) 0 R',c)):
        pre,b=re.split(rb'stream\r?\n',d[sn],maxsplit=1)
        if b'/FlateDecode' in pre:b=zlib.decompress(b)
        else:b=b.split(b'endstream',1)[0]
        yield sn,b
pages={'OpenAIQRH':[4,198-1],'FKS':[2,7,8,24,25,26],'CH2':[3,35,41,42,43,44,46,47],
       'PlattTrudgianFiniteRH':[2,4,5],'PlattTrudgian1809.03134v2':[1,3,4,11],
       'DudekPlatt1407.1901v1':[2,8,9,10],'Dusart2018':[11,13,15,17,18,19,20]}
for s,pp in pages.items():
    p=Path('/corpus/originals')/(s+'.pdf')
    d=objects(p.read_bytes())
    def walk(n):
        k=re.search(rb'/Kids\s*\[(.*?)\]',d[n],re.S)
        return [n] if k is None else sum((walk(c) for c in map(int,re.findall(rb'(\d+) 0 R',k[1]))),[])
    root=next(n for n,v in d.items() if re.search(rb'/Type\s*/Pages\b',v) and b'/Kids' in v and b'/Parent' not in v)
    leaves=walk(root)
    for j in pp:
        pg=leaves[j-1]
        print(s,j,pg,[(n,hashlib.sha256(b).hexdigest()) for n,b in streams(d,pg)])
        for n,b in streams(d,pg):
            lines=b.decode('latin1').split('\n')
            indices=list(range(404,428)) if s=='PlattTrudgianFiniteRH' and j==4 and n==114 else []
            if s=='FKS' and j==7:indices=[i for i,l in enumerate(lines) if '1, ' in l or 'Theorem' in l or '2.7' in l]
            if s=='CH2' and j==35:indices=[i for i,l in enumerate(lines) if '79059275' in l or '750902' in l or '758582' in l or '787' in l]
            for i in indices:
                for k in (range(i-6,i+7) if s=='CH2' else [i]):
                    print(k+1,repr(lines[k]))
