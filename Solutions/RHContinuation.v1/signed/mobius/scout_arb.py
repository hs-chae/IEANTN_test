#!/usr/bin/env python3
"""Directed-ball quadrature feasibility, not source-first PV or Lean verification."""
from flint import acb,arb,ctx
from pathlib import Path
import json,time,argparse,resource,hashlib
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();ctx.prec=64;rows=[];sigma=arb(49)/50
for start,width in [(0,10),(100,10),(10000,1),(10000,10),(100000,1),(100000,10),(26000000,1),(26000000,10)]:
 calls=[0,0]
 def f(z,analytic):
  calls[bool(analytic)]+=1
  v=(acb(sigma)+acb(0,1)*z).zeta()*(acb(sigma)-acb(0,1)*z).zeta()
  return 1/v.sqrt(analytic=analytic)
 t=time.monotonic();r=acb.integral(f,start,start+width,rel_tol=arb('0.001'),abs_tol=arb('0.001'),eval_limit=200000,depth_limit=40);seconds=time.monotonic()-t;row={'start':start,'width':width,'enclosure':str(r),'finite':r.is_finite(),'seconds':seconds,'calls':calls,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss};rows.append(row);a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps({'status':'SCOUT_IN_PROGRESS','python_flint':'0.9.0','precision_bits':ctx.prec,'rows':rows,'source_first_PV':False,'kernel_verified':False},indent=2)+'\n');print(json.dumps(row),flush=True)
a.out.write_text(json.dumps({'status':'SCOUT_COMPLETED','python_flint':'0.9.0','precision_bits':ctx.prec,'rows':rows,'source_first_PV':False,'kernel_verified':False},indent=2)+'\n')
