#!/usr/bin/env python3
"""Combine the reviewed English reports into one standalone reading copy.

Mathematical content is preserved; the identical verification section appears once.
The three historical input files and their original evidence remain unchanged.
"""
import hashlib
from html import escape
import json
from pathlib import Path
import re
from urllib.parse import urljoin

HERE = Path(__file__).resolve().parent
PUBLICATION = "86b232f17321b77cdbd7f63b4febb020a81560b9"
BASE = "https://github.com/hs-chae/IEANTN_test/blob/" + PUBLICATION + "/Solutions/RHOnePrimeEvolution.v1/reports/"
INPUTS = [("paper", "RH_PAPER_SUMMARY_EN.html"),
          ("frontier", "RH_ONE_PRIME_FRONTIER_EN.html"),
          ("network", "RH_NETWORK_EVOLUTION_EN.html")]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    source = {prefix: (HERE / name).read_text() for prefix, name in INPUTS}
    styles = [re.search(r"<style>(.*?)</style>", text, re.S).group(1)
              for text in source.values()]
    need(len(set(styles)) == 1, "Input reports have different styles")
    common = [re.search(r'<section id="verification">.*?</section>', source[p], re.S).group()
              for p in ("frontier", "network")]
    need(common[0] == common[1], "Verification sections differ; do not silently discard content")
    need("<math" not in common[0], "Verification deduplication needs a revised formula inventory")

    def links(text, prefix):
        text = re.sub(r'\bid="([^"]+)"', lambda m: 'id="' + prefix + '-' + m.group(1) + '"', text)
        def href(match):
            value = match.group(1)
            if value.startswith("#"):
                value = "#verification" if value == "#verification" else "#" + prefix + "-" + value[1:]
            elif not re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", value):
                value = urljoin(BASE, value)
            return 'href="' + value + '"'
        return re.sub(r'href="([^"]*)"', href, text)

    sections = {}
    for prefix, text in source.items():
        match = re.search(r"<main><header>.*?</header>(.*?)<footer>", text, re.S)
        need(match is not None, "Unexpected input document structure")
        body = match.group(1)
        if prefix != "paper":
            need(body.count(common[0]) == 1, "Common section missing or repeated")
            body = body.replace(common[0], "")
            body = body.replace("<h2>", "<h3>").replace("</h2>", "</h3>")
        sections[prefix] = links(body, prefix)

    verification = re.sub(r'href="(\.\.[^"]*)"',
                          lambda m: 'href="' + urljoin(BASE, m.group(1)) + '"', common[0])
    style = styles[0].replace("#lee", "#frontier-lee")
    style += "\n.chapter{margin-top:2.5rem}.chapter>h2{font-size:1.7rem;color:#173b71;border-bottom:3px solid #d7e4f7;padding-bottom:.6rem}.chapter section>h3{font-size:1.35rem;margin-top:0}.reading-note{font-size:.95rem}details.contents{background:#fff;border:1px solid #d7e4f7;border-radius:12px;padding:1rem;margin:1rem 0}details.contents summary{cursor:pointer;font-weight:700}details.contents nav{margin-top:1rem}\n"
    toc = []
    for prefix in ("frontier", "network"):
        for identity, heading in re.findall(r'<section id="([^"]+)"><h3>(.*?)</h3>', sections[prefix], re.S):
            toc.append('<a href="#' + escape(identity, quote=True) + '">' + heading + '</a>')
    header = '''<header id="top"><p class="status">Complete English report · source-conditional results · offline mathematics</p>
<h1>RH one-prime and network evolution</h1>
<p class="reading-note">Read the summary first, then use the links below for the full prime-interval results, network consequences, or proof and reproduction details. All three English accounts are collected here; the shared verification section appears once.</p>
<nav aria-label="Main sections"><a href="#paper-summary">Summary</a><a href="#prime-frontier">Prime intervals</a><a href="#network-evolution">Network results</a><a href="#verification">Proofs and reproduction</a></nav></header>'''
    contents = '<details class="contents"><summary>Detailed contents</summary><nav aria-label="Detailed sections">' + ''.join(toc) + '</nav></details>'
    body = (header + sections["paper"] + contents
            + '<article class="chapter" id="prime-frontier"><h2>1. Prime intervals and the Gaussian witness</h2>' + sections["frontier"] + '</article>'
            + '<article class="chapter" id="network-evolution"><h2>2. Mathematical consequences across the network</h2>' + sections["network"] + '</article>'
            + verification
            + '<footer><p>Static MathML · embedded STIX font · no network needed to read.</p><p>Mathematical source: 109729571ac5e6ea38944c965abad11a8dad4d43. Reproduction and source links point to the reviewed publication.</p><p><a href="#top">Return to the beginning</a></p></footer>')
    html = '<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>RH one-prime and network evolution — complete report</title><style>' + style + '</style></head><body><main>' + body + '</main></body></html>'
    expected = [m for _, name in INPUTS for m in re.findall(r'<math\b.*?</math>', (HERE / name).read_text(), re.S)]
    actual = re.findall(r'<math\b.*?</math>', html, re.S)
    need(actual == expected and len(actual) == 127, "A mathematical display changed")
    ids = re.findall(r'\bid="([^"]+)"', html)
    need(len(ids) == len(set(ids)), "Duplicate section identity")
    need(all(x in set(ids) for x in re.findall(r'href="#([^"]+)"', html)), "Unresolved internal link")
    output = HERE / "RH_COMPLETE_REPORT_EN.html"
    output.write_text(html)
    receipt = dict(status="PRESENTATION_ONLY_CONSOLIDATION_MATHML_BYTE_IDENTICAL",
                   output=output.name, sha256=digest(output.read_bytes()), bytes=output.stat().st_size,
                   mathml_blocks=len(actual), duplicate_verification_removed=True,
                   inputs=[dict(path=n, sha256=digest((HERE/n).read_bytes())) for _, n in INPUTS],
                   source_publication=PUBLICATION, script_sha256=digest(Path(__file__).read_bytes()))
    (HERE / "COMPLETE_REPORT_BUILD.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
