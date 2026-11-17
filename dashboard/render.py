"""Rebuild the proof dashboard from its mathematical statements and dependencies."""
import argparse
from collections import Counter
from html import escape
import json
from pathlib import Path
import re
from urllib.parse import unquote
from math_markdown import protect

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
STATES = {
    "kernel": ("Kernel checked", "#15786d"),
    "public": ("Upstream proof", "#4e70a9"),
    "typed": ("Header only", "#dda946"),
    "binding": ("Open application", "#bd7152"),
    "missing": ("Needs a header", "#8e9caa"),
}
NODES = {
    "signed-shimura-representative": ("marked", "Marked Jacobian"),
    "signed-printed-field": ("field", "Field of the marked action"),
    "signed-global-stable-height": ("formula", "Global stable-height formula"),
    "signed-period-formula": ("height", "Six-contact height bound"),
    "rational-jacobian-conductor": ("local", "Local reduction"),
    "two-printed-rank-results": ("rank", "Selected elliptic twists"),
    "signed-jacobian-original-endpoint": ("target", "Bounded polynomial theorem"),
}


def tally(rows):
    return Counter(r["state"] for r in rows)


def chapter_path(i):
    return f"chapters/{i + 1:02d}.md"


def table(groups, base):
    rows = ["| Chapter | Kernel checked | Upstream proof | Header only | Open application | Needs a header |",
            "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for i, (name, items) in enumerate(groups.items()):
        t = tally(items)
        rest = " | ".join(str(t[state]) for state in list(STATES)[1:])
        rows.append(f"| [{name}]({base}{chapter_path(i)}) | {t['kernel']}/{len(items)} ({t['kernel']/len(items):.0%}) | {rest} |")
    return "\n".join(rows)


def diagram(by_id):
    lines = ["```mermaid", "flowchart LR"]
    for ident, (key, label) in NODES.items():
        style = "checked" if by_id[ident]["state"] == "kernel" else "pending"
        lines.append(f'    {key}["{label}"]:::{style}')
    for ident, (key, _) in NODES.items():
        for parent in by_id[ident]["needs"]:
            if parent in NODES:
                lines.append(f"    {NODES[parent][0]} --> {key}")
    return "\n".join(lines + ["    classDef checked fill:#dff2ec,stroke:#247669,color:#12392f",
                               "    classDef pending fill:#fff0d2,stroke:#966b22,color:#49340f", "```"])


def route_chart(routes, rows):
    lines = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 880 330" role="img" aria-labelledby="title desc">',
             '<title id="title">Formalization by construction</title>',
             '<desc id="desc">Each bar gives the proportions of five proof states. The right column counts kernel-checked packages out of all packages on that route.</desc>',
             '<rect width="880" height="330" rx="12" fill="#f2f6f4"/>',
             '<g font-family="Inter,system-ui,sans-serif" fill="#193a33">',
             '<text x="20" y="32" font-size="20" font-weight="700">Formalization by construction</text>',
             '<text x="858" y="31" text-anchor="end" font-size="13">Kernel checked / packages</text>']
    for i, route in enumerate(routes):
        subset = [r for r in rows if route in r["routes"]]
        c = tally(subset)
        y, offset = 63 + i * 35, 0
        lines.append(f'<text x="20" y="{y+4}" font-size="14">{escape(route)}</text>')
        for state, (label, color) in STATES.items():
            if c[state]:
                start, width = 217 + 544 * offset / len(subset), 544 * c[state] / len(subset)
                lines.append(f'<rect x="{start:.2f}" y="{y-9}" width="{width:.2f}" height="15" fill="{color}"><title>{escape(label)} · {c[state]}</title></rect>')
                offset += c[state]
        lines.append(f'<text x="858" y="{y+4}" text-anchor="end" font-size="15" font-weight="650">{c["kernel"]} / {len(subset)}</text>')
    for x, (label, color) in zip((20, 194, 377, 533, 715), STATES.values()):
        lines += [f'<rect x="{x}" y="296" width="13" height="13" fill="{color}"/>',
                  f'<text x="{x+19}" y="308" font-size="13">{label}</text>']
    return "\n".join(lines + ["</g></svg>"])


def section(s, key, body):
    first, last = f"<!-- {key}:begin -->", f"<!-- {key}:end -->"
    if s.count(first) != 1 or s.count(last) != 1:
        raise ValueError("Missing or duplicate README section " + key)
    a, rest = s.split(first)
    return a + first + "\n\n" + body + "\n\n" + last + rest.split(last)[1]


def verify_links(files):
    for path, data in files.items():
        if path.suffix != ".md":
            continue
        for link in re.findall(r"\]\(([^)\n]+)\)", data):
            rel = unquote(link.split("#")[0].split("?")[0])
            if not rel or "://" in rel or rel.startswith("mailto:"):
                continue
            target = (path.parent / rel).resolve()
            if not target.is_relative_to(ROOT) or (target not in files and not target.exists()):
                raise ValueError(f"{path.relative_to(ROOT)} links to a missing file: {link}")


def main(write):
    data = json.loads((HERE / "packages.json").read_bytes())
    rows, links = data["packages"], data["declarations"]
    by_id = {r["id"]: r for r in rows}
    groups = {name: [r for r in rows if r["chapter"] == name] for name in data["chapters"]}
    if len(by_id) != len(rows) or sum(map(len, groups.values())) != len(rows):
        raise ValueError("Invalid package identifiers or chapter membership")
    for r in rows:
        if r["state"] not in STATES or set(r["needs"]) - by_id.keys() or set(r["routes"]) - set(data["routes"]):
            raise ValueError("Invalid package " + r["id"])
    for name, loc in links.items():
        base, n = loc.rsplit("#L", 1)
        p = ROOT / base
        if not p.is_file() or name.split(".")[-1] not in p.read_text().splitlines()[int(n)-1]:
            raise ValueError("Invalid declaration link for " + name)
    c = tally(rows)
    summary = (f"**{c['kernel']}/{len(rows)} packages have a locally kernel-checked deduction.** "
               f"{c['public']} are classified from pinned upstream proofs, {c['typed']} have only a formal header, "
               f"{c['binding']} await an application or identification, and {c['missing']} need a Lean statement.")
    readme = (ROOT / "README.md").read_text()
    for key, body in (("summary", summary), ("chapters", table(groups, "dashboard/")), ("graph", diagram(by_id))):
        readme = section(readme, key, body)
    meanings = [("Kernel checked", "The formalization records a local kernel check of a lemma or a conditional implication."),
                ("Upstream proof", "An existing proof in the indicated upstream Lean development supplies the deduction."),
                ("Header only", "Lean expresses the proposed statement with its hypotheses and conclusion. Its proof remains to be supplied."),
                ("Open application", "A proof still needs an identification or a specialization to the objects of the construction."),
                ("Needs a header", "The mathematical task has been identified and still needs a Lean statement.")]
    deck = ["# Proof dashboard", "", summary, "", "[Search the interactive explorer](index.html?raw=1) · [Mathematical blueprint](../docs/theorem-blueprint.md)", "",
            "## Completion by chapter", "", table(groups, ""), "", "## Reading the states", ""]
    for label, definition in meanings:
        deck.append(f"- **{label}.** {definition}")
    deck.extend(["", "Each chapter lists its statements, prerequisites and named declarations. "
                       "A source link is given when the declaration can be located unambiguously in this edition. "
                       "Several named declarations may support one package."])
    output = {ROOT / "README.md": readme, HERE / "README.md": "\n".join(deck),
              HERE / "routes.svg": route_chart(data["routes"], rows)}
    locations = {r["id"]: f"{i+1:02d}.md#{r['id']}" for i, group in enumerate(groups.values()) for r in group}
    for i, (title, subset) in enumerate(groups.items()):
        lines = ["# " + title, "", "[All chapters](../README.md) · [Interactive explorer](../index.html?raw=1)"]
        for r in subset:
            lines.extend(["", f'<a id="{r["id"]}"></a>', "", "## " + r["title"], "",
                          f"**{STATES[r['state']][0]}.** {r['claim']}"])
            if r["needs"]:
                deps = [f"[{by_id[n]['title']}]({locations[n]})" for n in r["needs"]]
                lines.extend(["", "Prerequisites · " + " · ".join(deps)])
            if r["headers"]:
                decls = [f"[`{h}`](../../{links[h]})" if h in links else f"`{h}`" for h in r["headers"]]
                lines.extend(["", "<details>", "<summary>Lean declarations</summary>", "", "\n".join("- " + h for h in decls), "", "</details>"])
        output[HERE / chapter_path(i)] = "\n".join(lines)
    payload = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c")
    template = (HERE / "template.html").read_text()
    if template.count("__BLUEPRINT_DATA__") != 1:
        raise ValueError("Invalid dashboard template")
    output[HERE / "index.html"] = template.replace("__BLUEPRINT_DATA__", payload)
    for p in [*ROOT.glob("docs/*.md"), ROOT / "bounded/README.md"]:
        output[p] = p.read_text()
    verify_links(output)
    for p, value in output.items():
        value = value.rstrip() + "\n"
        if p.suffix == ".md" and protect(value)[0] != value:
            raise ValueError(f"Unprotected TeX in {p.relative_to(ROOT)}")
        if write:
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(value)
        elif not p.is_file() or p.read_text() != value:
            raise SystemExit("Dashboard needs regeneration: " + str(p.relative_to(ROOT)))
    print(f"Verified {len(rows)} packages, {sum(len(r['needs']) for r in rows)} prerequisite links and {len(links)} declaration locations.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true")
    main(ap.parse_args().write)
