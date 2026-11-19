#!/usr/bin/env python3
"""Embed a licensed local math font; preserve every accepted MathML byte."""
from pathlib import Path
import argparse,base64,hashlib,json,re
R=Path(__file__).resolve().parents[1]
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);a=p.parse_args()
 if a.receipt.exists() or a.input.resolve()==a.output.resolve():raise ValueError('fresh receipt and distinct output required')
 original=a.input.read_bytes();text=original.decode();font=(R/'reports/fonts/STIXGeneral.ttf').read_bytes();license=(R/'reports/fonts/LICENSE_STIX').read_bytes()
 if len(font)!=448228 or not license or text.count('</head>')!=1 or text.count('style-src &#39;unsafe-inline&#39;;')!=1 or 'font-src' in text:raise ValueError('expected font/header frame differs')
 nodes=re.findall(r'<math\b[^>]*>.*?</math>',text,re.S)
 if not nodes:raise ValueError('static MathML required')
 css='<style>/*'+license.decode()+'*/@font-face{font-family:"IEANTN Offline Math";src:url(data:font/ttf;base64,'+base64.b64encode(font).decode()+') format("truetype");font-style:normal;font-weight:400}body{overflow-wrap:anywhere}math{font-family:"IEANTN Offline Math",serif!important}</style>'
 result=text.replace('style-src &#39;unsafe-inline&#39;;','style-src &#39;unsafe-inline&#39;; font-src data:;',1).replace('</head>',css+'</head>',1)
 if re.findall(r'<math\b[^>]*>.*?</math>',result,re.S)!=nodes:raise ValueError('MathML bytes changed')
 a.output.write_text(result);a.receipt.parent.mkdir(parents=True,exist_ok=True)
 a.receipt.write_text(json.dumps({'status':'PASS_SELF_CONTAINED_MATH_FONT_ALL_MATHML_BYTES_UNCHANGED','input_sha256':sha(original),'output_sha256':sha(result.encode()),'font_sha256':sha(font),'font_license_sha256':sha(license),'mathml_nodes_unchanged':len(nodes),'producer_sha256':sha(Path(__file__).read_bytes()),'network_assets':False,'mathematical_change':False},indent=2)+'\n')
 print(json.dumps({'output_sha256':sha(result.encode()),'mathml_nodes':len(nodes),'bytes':len(result.encode())}))
if __name__=='__main__':main()
