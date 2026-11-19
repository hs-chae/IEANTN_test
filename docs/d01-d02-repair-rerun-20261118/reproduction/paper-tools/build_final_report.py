#!/usr/bin/env python3
r"""Offline Markdown -> HTML with static, deliberately restricted MathML.

Dependency: markdown-it-py==4.0.0. No browser, JS, CDN or network is used.
Math delimiters: \(...\), \[...\], $...$, and standalone $$...$$.
Code spans/fences are literal. Unknown commands/malformed math fail before output
replacement. The parser derives from coordinator/unscored-mertens/build_draft.py;
it copies no research content and does not execute that manuscript builder.
"""
from __future__ import annotations

import argparse
import hashlib
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import urllib.parse
import xml.etree.ElementTree as ET

from markdown_it import MarkdownIt
from markdown_it.token import Token

MATH_NS = "http://www.w3.org/1998/Math/MathML"
TOKEN = re.compile(r"\\[A-Za-z]+|\\.|[0-9]+(?:\.[0-9]+)?|[A-Za-z]|[^\s]")
SYMBOLS = {
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "eta": "η",
    "theta": "θ", "vartheta": "ϑ", "psi": "ψ", "pi": "π", "rho": "ρ",
    "sigma": "σ", "epsilon": "ϵ", "varepsilon": "ε", "lambda": "λ",
    "zeta": "ζ", "tau": "τ", "mu": "μ", "Lambda": "Λ", "Delta": "Δ",
    "Gamma": "Γ", "Omega": "Ω", "infty": "∞", "le": "≤", "leq": "≤",
    "ge": "≥", "geq": "≥", "lt": "<", "gt": ">", "ne": "≠", "neq": "≠",
    "to": "→", "rightarrow": "→", "Rightarrow": "⇒", "iff": "⇔",
    "cdot": "·", "times": "×", "pm": "±", "in": "∈", "notin": "∉",
    "forall": "∀", "exists": "∃", "subseteq": "⊆", "cup": "∪", "cap": "∩",
    "lfloor": "⌊", "rfloor": "⌋", "lceil": "⌈", "rceil": "⌉",
    "lvert": "|", "rvert": "|", "vert": "|", "lVert": "‖", "rVert": "‖",
    "ldots": "…", "dots": "…", "cdots": "⋯", "{": "{", "}": "}",
    "%": "%", "_": "_", "#": "#", "&": "&",
}
GREEK = set("alpha beta gamma delta eta theta vartheta psi pi rho sigma epsilon varepsilon lambda zeta tau mu Lambda Delta Gamma Omega".split())
FUNCTIONS = set("log ln exp min max sin cos tan lim sup inf gcd Re Im".split())
SPACES = {",": "0.16em", ";": "0.28em", " ": "0.25em", "!": "0em", "qquad": "2em", "quad": "1em"}
SIZES = {"left", "right", "big", "Big", "bigl", "bigr", "Bigl", "Bigr"}


class RenderError(ValueError):
    pass


def tag(name, content, **attrs):
    attributes = "".join(f' {key}="{html.escape(str(value), quote=True)}"' for key, value in attrs.items())
    return f"<{name}{attributes}>{content}</{name}>"


class Formula:
    def __init__(self, source):
        self.source = source
        matches = list(TOKEN.finditer(source))
        self.tokens = [match.group() for match in matches]
        self.spans = [(match.start(), match.end()) for match in matches]
        self.pos = 0
        self.sized_delimiters = 0

    def take(self):
        if self.pos >= len(self.tokens):
            raise RenderError("Unexpected end of formula")
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def argument(self):
        if self.pos >= len(self.tokens):
            raise RenderError("Missing formula argument")
        token = self.tokens[self.pos]
        if token == "{":
            self.pos += 1
            value = self.row(stop=True)
            if self.take() != "}":
                raise RenderError("Unclosed formula group")
            return value
        # TeX's unbraced argument is one digit even when the lexer groups 38.
        if re.fullmatch(r"[0-9]{2,}", token):
            self.tokens[self.pos] = token[1:]
            return tag("mn", token[0])
        return self.atom()

    def text_argument(self):
        if self.pos >= len(self.tokens) or self.tokens[self.pos] != "{":
            raise RenderError("Text/operator argument must be braced")
        start = self.spans[self.pos][1]
        self.pos += 1
        while self.pos < len(self.tokens) and self.tokens[self.pos] != "}":
            if self.tokens[self.pos] == "{":
                raise RenderError("Nested groups in text/operator arguments are unsupported")
            self.pos += 1
        if self.pos >= len(self.tokens):
            raise RenderError("Unclosed text/operator argument")
        value = self.source[start:self.spans[self.pos][0]]
        self.pos += 1
        if "\\" in value or "$" in value:
            raise RenderError("Commands or nested math in text/operator arguments are unsupported")
        return html.escape(value)

    def atom(self):
        token = self.take()
        if token == "{":
            value = self.row(stop=True)
            if self.take() != "}":
                raise RenderError("Unclosed formula group")
            return value
        if token.startswith("\\"):
            command = token[1:]
            if command in SIZES:
                allowed = {"(", ")", "[", "]", "|", r"\{", r"\}", r"\lvert", r"\rvert", r"\vert", r"\lVert", r"\rVert", r"\lfloor", r"\rfloor", r"\lceil", r"\rceil"}
                if self.pos >= len(self.tokens) or self.tokens[self.pos] not in allowed:
                    raise RenderError("Unsupported or missing sizing delimiter after " + token)
                if command == "left":
                    self.sized_delimiters += 1
                elif command == "right":
                    if self.sized_delimiters <= 0:
                        raise RenderError("Unmatched right delimiter")
                    self.sized_delimiters -= 1
                return self.atom()
            if command in {"frac", "tfrac", "dfrac"}:
                return tag("mfrac", self.argument() + self.argument())
            if command == "sqrt":
                if self.pos < len(self.tokens) and self.tokens[self.pos] == "[":
                    raise RenderError("Indexed square roots are unsupported")
                return tag("msqrt", self.argument())
            if command in FUNCTIONS:
                return tag("mi", command, mathvariant="normal")
            if command == "text":
                return tag("mtext", self.text_argument())
            if command == "operatorname":
                return tag("mi", self.text_argument(), mathvariant="normal")
            if command in {"mathrm", "mathbf", "mathbb", "mathcal"}:
                variant = {"mathrm": "normal", "mathbf": "bold", "mathbb": "double-struck", "mathcal": "script"}[command]
                return tag("mstyle", self.argument(), mathvariant=variant)
            if command in {"sum", "prod", "int"}:
                return tag("mo", {"sum": "∑", "prod": "∏", "int": "∫"}[command], largeop="true")
            if command in SPACES:
                return f'<mspace width="{SPACES[command]}"></mspace>'
            if command in SYMBOLS:
                return tag("mi" if command in GREEK else "mo", html.escape(SYMBOLS[command]))
            raise RenderError("Unsupported formula command: " + token)
        if token in {"}", "^", "_", "$", "%", "#", "&", "`", "\\"}:
            raise RenderError("Unexpected or unsupported formula token: " + token)
        if re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", token):
            return tag("mn", token)
        if token.isalpha():
            return tag("mi", html.escape(token))
        return tag("mo", html.escape("−" if token == "-" else token))

    def row(self, stop=False):
        values = []
        while self.pos < len(self.tokens):
            if stop and self.tokens[self.pos] == "}":
                break
            base = self.atom()
            sub = sup = None
            while self.pos < len(self.tokens) and self.tokens[self.pos] in {"_", "^"}:
                kind = self.take()
                value = self.argument()
                if kind == "_":
                    if sub is not None:
                        raise RenderError("Repeated subscript")
                    sub = value
                else:
                    if sup is not None:
                        raise RenderError("Repeated superscript")
                    sup = value
            if sub is not None and sup is not None:
                base = tag("msubsup", base + sub + sup)
            elif sub is not None:
                base = tag("msub", base + sub)
            elif sup is not None:
                base = tag("msup", base + sup)
            values.append(base)
        return tag("mrow", "".join(values))


def math(source, display=False):
    if not source.strip():
        raise RenderError("Empty math formula")
    parser = Formula(source)
    body = parser.row()
    if parser.pos != len(parser.tokens):
        raise RenderError("Unconsumed formula tokens")
    if parser.sized_delimiters:
        raise RenderError("Unclosed left delimiter")
    result = f'<math xmlns="{MATH_NS}" display="{"block" if display else "inline"}">{body}</math>'
    ET.fromstring(result)
    return result


def closing(source, delimiter, start):
    while True:
        pos = source.find(delimiter, start)
        if pos < 0:
            return -1
        before = pos
        while before > 0 and source[before - 1] == "\\":
            before -= 1
        if (pos - before) % 2 == 0:
            return pos
        start = pos + len(delimiter)


def inline_math(state, silent):
    start = state.pos
    if state.src.startswith("\\(", start):
        opener, closer = "\\(", "\\)"
    elif state.src.startswith("$", start):
        if state.src.startswith("$$", start):
            raise RenderError("Display math must start on its own Markdown line")
        opener = closer = "$"
    else:
        if re.match(r"\\(?:[A-Za-z]+|[()[\]])", state.src[start:]):
            raise RenderError("TeX command/delimiter outside math; use math delimiters or a code span")
        return False
    end = closing(state.src, closer, start + len(opener))
    if end < 0 or end + len(closer) > state.posMax:
        raise RenderError("Unclosed inline math delimiter: " + opener)
    if closer == "$" and state.src.startswith("$$", end):
        raise RenderError("Mismatched inline/display dollar delimiters")
    content = state.src[start + len(opener):end]
    if not silent:
        token = state.push("report_math_inline", "math", 0)
        token.content = math(content)
    state.pos = end + len(closer)
    return True


def block_math(state, startLine, endLine, silent):
    if state.is_code_block(startLine):
        return False
    first = state.src[state.bMarks[startLine] + state.tShift[startLine]:state.eMarks[startLine]]
    if first.startswith("$$"):
        opener = closer = "$$"
    elif first.startswith("\\["):
        opener, closer = "\\[", "\\]"
    else:
        return False
    if silent:
        return True
    chunks = []
    for line in range(startLine, endLine):
        value = state.src[state.bMarks[line] + state.tShift[line]:state.eMarks[line]]
        if line == startLine:
            value = value[len(opener):]
        end = closing(value, closer, 0)
        if end >= 0:
            if value[end + len(closer):].strip():
                raise RenderError("Text after a display-math closing delimiter is unsupported")
            chunks.append(value[:end])
            token = state.push("report_math_block", "div", 0)
            token.content = math("\n".join(chunks), True)
            token.map = [startLine, line + 1]
            state.line = line + 1
            return True
        chunks.append(value)
    raise RenderError("Unclosed display math delimiter: " + opener)


def structure(state):
    for index, token in enumerate(state.tokens):
        if token.type == "heading_open":
            token.attrSet("id", f"section-{index}")
        if token.type != "blockquote_open" or index + 2 >= len(state.tokens):
            continue
        first = state.tokens[index + 2]
        if first.type != "inline":
            continue
        match = re.match(r"^\[!(NOTE|TIP|IMPORTANT|WARNING|CAUTION)\](?:\s|$)", first.content)
        if not match:
            continue
        kind = match.group(1).lower()
        token.attrSet("class", "card card-" + kind)
        token.attrSet("role", "note")
        # This rule runs before MarkdownIt's inline parsing.
        first.content = "**" + kind.title() + ".** " + first.content[match.end():].lstrip()


class Readback(HTMLParser):
    def __init__(self):
        super().__init__()
        self.exempt = 0
        self.visible = []
        self.math_count = 0

    def handle_starttag(self, name, attrs):
        if name in {"script", "iframe", "img", "link", "object", "embed"}:
            raise RenderError("Active/external rendering element is forbidden: " + name)
        if name in {"code", "pre", "math", "style"}:
            self.exempt += 1
        if name == "math":
            self.math_count += 1

    def handle_endtag(self, name):
        if name in {"code", "pre", "math", "style"}:
            self.exempt -= 1

    def handle_data(self, value):
        if not self.exempt:
            self.visible.append(value)


def render(source, title, css, source_href):
    md = MarkdownIt("commonmark", {"html": False, "linkify": False, "typographer": False}).enable("table")
    md.inline.ruler.before("escape", "report_math", inline_math)
    md.block.ruler.before("fence", "report_math", block_math, {"alt": ["paragraph", "reference", "blockquote", "list"]})
    md.core.ruler.before("inline", "report_structure", structure)
    md.add_render_rule("report_math_inline", lambda self, tokens, idx, options, env: tokens[idx].content)
    md.add_render_rule("report_math_block", lambda self, tokens, idx, options, env: '<div class="equation">' + tokens[idx].content + '</div>\n')
    md.add_render_rule("table_open", lambda self, tokens, idx, options, env: '<div class="table-scroll" role="region" aria-label="Report table" tabindex="0"><table>\n')
    md.add_render_rule("table_close", lambda self, tokens, idx, options, env: '</table></div>\n')
    def no_image(*args):
        raise RenderError("Images are unsupported: the report must be self-contained without assets")
    md.add_render_rule("image", no_image)
    body = md.render(source)
    result = ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
              '<meta name="viewport" content="width=device-width,initial-scale=1">'
              '<meta http-equiv="Content-Security-Policy" content="default-src &#39;none&#39;; style-src &#39;unsafe-inline&#39;; base-uri &#39;none&#39;; form-action &#39;none&#39;">'
              '<title>' + html.escape(title) + '</title><style>' + css + '</style></head>\n'
              '<body><a class="skip" href="#report">Skip to report</a><main id="report"><article>' + body + '</article>'
              '<footer>Static offline report. Equations use presentation MathML; no JavaScript, CDN or downloaded font is required. '
              '<a href="' + html.escape(source_href, quote=True) + '">Markdown source</a></footer></main></body></html>\n')
    audit = Readback()
    audit.feed(result)
    if audit.exempt != 0:
        raise RenderError("Unbalanced code/math elements in output")
    if re.search(r"\\(?:[A-Za-z]+|[()[\]])|\$\$", "".join(audit.visible)):
        raise RenderError("Unrendered TeX outside code in output")
    return result, audit.math_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--title", default=None)
    args = parser.parse_args()
    source = args.input.resolve(strict=True)
    output = args.output.resolve()
    css_path = Path(__file__).resolve().with_name("final_report.css")
    if output in {source, css_path.resolve()}:
        raise RenderError("Output must not overwrite Markdown input or renderer CSS")
    css = css_path.read_text(encoding="utf-8")
    if re.search(r"@import|url\s*\(|</style", css, re.I):
        raise RenderError("CSS must not load assets or close its style element")
    href = urllib.parse.quote(os.path.relpath(source, output.parent), safe="/._-~")
    rendered, count = render(source.read_text(encoding="utf-8"), args.title or source.stem.replace("_", " "), css, href)
    data = rendered.encode("utf-8")
    output.parent.mkdir(parents=True, exist_ok=True)
    name = None
    try:
        with tempfile.NamedTemporaryFile(prefix="." + output.name + ".", dir=output.parent, delete=False) as stream:
            name = stream.name
            stream.write(data)
        os.replace(name, output)
    finally:
        if name is not None and Path(name).exists():
            Path(name).unlink()
    print(json.dumps({"status": "PASS", "mathml_formulas": count, "output_sha256": hashlib.sha256(data).hexdigest()}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (RenderError, OSError, ET.ParseError) as error:
        print("error: " + str(error), file=sys.stderr)
        sys.exit(2)
