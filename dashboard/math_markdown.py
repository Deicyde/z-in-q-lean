"""Preserve TeX in GitHub Markdown and compare it with GitHub's rendered math nodes."""
import argparse
from html.parser import HTMLParser
from pathlib import Path
import re


def github_tex(tex):
    # GitHub's math renderer rejects \operatorname even when Markdown preserves
    # every byte. All named operators in the reading edition have upright names.
    return re.sub(r"\\operatorname\{([A-Za-z]+)\}", r"\\mathrm{\1}", tex)


def inline(line, expressions):
    result = []
    i = 0
    while i < len(line):
        if line.startswith(r"\$", i):
            result.append(line[i:i+2])
            i += 2
        elif line[i] == "`":
            n = len(line[i:]) - len(line[i:].lstrip("`"))
            end = line.find("`" * n, i + n)
            if end < 0:
                result.append(line[i:])
                break
            result.append(line[i:end+n])
            i = end + n
        elif line[i] == "$":
            protected = line.startswith("$`", i)
            start = i + (2 if protected else 1)
            close = "`$" if protected else "$"
            j = start
            while True:
                end = line.find(close, j)
                if end < 0:
                    raise ValueError("Unclosed inline equation: " + line.rstrip()[:120])
                backslashes = end - len(line[:end].rstrip("\\"))
                if protected or backslashes % 2 == 0:
                    break
                j = end + 1
            tex = github_tex(line[start:end])
            if not tex.strip() or "`" in tex:
                raise ValueError("Invalid inline equation: " + line.rstrip()[:120])
            # GitHub HTML-escapes a literal comparison sign twice inside an inline
            # code span. Use the equivalent TeX relation before protecting the span.
            tex = re.sub(r"([<>])[ \t]*", lambda m: r"\lt " if m[1] == "<" else r"\gt ", tex)
            expressions.append(("inline", tex))
            result.append("$`" + tex + "`$")
            i = end + len(close)
        else:
            result.append(line[i])
            i += 1
    return "".join(result)


def protect(source):
    """Return safe Markdown and the exact TeX of each equation in document order."""
    out, expressions, display = [], [], []
    state, marker = "prose", ""
    for line in source.splitlines(keepends=True):
        s = line.strip()
        if state != "prose":
            end = s == "$$" if state == "dollars" else re.fullmatch(re.escape(marker[0]) + "{" + str(len(marker)) + ",}", s)
            if end:
                if state in ("math", "dollars"):
                    tex = github_tex("".join(display).strip())
                    if not tex:
                        raise ValueError("Empty display")
                    expressions.append(("display", tex))
                    out.extend(["```math\n", tex + "\n", "```\n"])
                else:
                    out.append(line)
                state, display = "prose", []
            elif state in ("math", "dollars"):
                if line.rstrip().endswith(r"\\"):
                    line = line.rstrip() + "[0pt]\n"
                display.append(line)
            else:
                out.append(line)
            continue
        fence = re.match(r"^ {0,3}(`{3,}|~{3,})([^\n]*)$", line.rstrip("\r\n"))
        if fence:
            marker = fence[1]
            state = "math" if fence[2].strip() == "math" else "code"
            if state == "code":
                out.append(line)
        elif s == "$$":
            state = "dollars"
        elif s.startswith("$$") and s.endswith("$$") and len(s) > 4:
            tex = github_tex(s[2:-2].strip())
            expressions.append(("display", tex))
            out.extend(["```math\n", tex + "\n", "```\n"])
        else:
            out.append(inline(line, expressions))
    if state != "prose":
        raise ValueError("Unclosed equation or code fence")
    return "".join(out), expressions


class Rendered(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.equations = []
        self.buffer = None
        self.kind = None

    def handle_starttag(self, tag, attrs):
        if tag == "math-renderer":
            classes = dict(attrs).get("class", "").split()
            self.kind = "display" if "js-display-math" in classes else "inline"
            self.buffer = []

    def handle_data(self, data):
        if self.buffer is not None:
            self.buffer.append(data)

    def handle_endtag(self, tag):
        if tag == "math-renderer" and self.buffer is not None:
            text = "".join(self.buffer).strip()
            mark = "$$" if self.kind == "display" else "$"
            if not (text.startswith(mark) and text.endswith(mark)):
                raise ValueError("Unrecognized GitHub math node")
            self.equations.append((self.kind, text[len(mark):-len(mark)].strip()))
            self.buffer = None


def verify(source, html=None):
    text = source.read_text()
    canonical, equations = protect(text)
    if text != canonical:
        raise ValueError(f"Math needs protected delimiters in {source.name}")
    if html:
        actual = Rendered()
        actual.feed(html.read_text())
        actual.close()
        if actual.buffer is not None or equations != actual.equations:
            raise ValueError(f"GitHub changed a TeX expression in {source.name}")
    return len(equations)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--html", type=Path, help="HTML from GitHub's Markdown API for this file")
    args = parser.parse_args()
    print(f"Verified {verify(args.source, args.html)} equations in {args.source.name}.")
