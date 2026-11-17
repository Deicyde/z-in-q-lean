"""Inventory local Lean sources and inspect the two advertised Lake targets (Python 3.11+)."""

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import tomllib

from lean_source import masked, project_sources


TOKENS = {
    "proofPlaceholder": re.compile(r"\b(?:sorry|admit|sorryAx)\b"),
    "declaredAxiom": re.compile(r"^\s*(?:(?:public|private|noncomputable)\s+)*axiom\s+", re.M),
    "compilerDecision": re.compile(r"\b(?:native_decide|ofReduceBool|trustCompiler)\b"),
    "unsafeDeclaration": re.compile(r"\bunsafe\s+(?:def|theorem|abbrev|opaque|instance)\b"),
}
IMPORT = re.compile(r"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+([\w.]+(?:[ \t]+[\w.]+)*)", re.M)


def local_modules(project, sources):
    manifest = tomllib.loads((project / "lakefile.toml").read_text())
    roots = set()
    search_dirs = set()
    for lib in manifest["lean_lib"]:
        directory = project / lib.get("srcDir", ".")
        search_dirs.add(directory)
        if lib["name"] in manifest["defaultTargets"]:
            roots.update(directory / (m.replace(".", "/") + ".lean")
                         for m in lib.get("roots", [lib["name"]]))
    if not roots or roots - sources.keys():
        raise ValueError(f"A default Lake target in {project.name} has a missing root")
    todo = list(roots)
    reached = set()
    for source in todo:
        if source in reached:
            continue
        reached.add(source)
        for group in IMPORT.findall(sources[source]):
            for name in group.split():
                path = name.replace(".", "/") + ".lean"
                candidates = [directory / path for directory in search_dirs if directory / path in sources]
                if len(candidates) > 1:
                    raise ValueError(f"Ambiguous local import {name} in {source}")
                todo.extend(candidates)
    return reached


def inventory(root):
    sources = {}
    lines = 0
    found = defaultdict(list)
    for path in project_sources(root):
        raw = path.read_text()
        lines += len(raw.splitlines())
        code = masked(raw)
        sources[path] = code
        for kind, pattern in TOKENS.items():
            for match in pattern.finditer(code):
                found[kind].append({"file": path.relative_to(root).as_posix(),
                                    "line": code.count("\n", 0, match.start()) + 1})
    targets = {}
    for project in (root, root / "bounded"):
        name = project.relative_to(root).as_posix()
        files = {p.relative_to(root).as_posix() for p in local_modules(project, sources)}
        targets[name] = {"localModules": len(files), "flagged": sorted(
            {row["file"] for rows in found.values() for row in rows if row["file"] in files})}
    return {"sourceFiles": len(sources), "sourceLines": lines, "defaultTargets": targets,
            "matches": {kind: found[kind] for kind in TOKENS}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps(inventory(args.root.resolve()), indent=2))
