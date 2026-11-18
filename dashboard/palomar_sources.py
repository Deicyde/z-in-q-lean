"""Report Palomar's repository-wide source header and physical-length checks."""
import argparse
import json
from pathlib import Path
import re

from lean_source import masked


def scan(root):
    problems = {"missingModule": [], "overLength": [], "symlinks": []}
    counts = {"files": 0, "withModule": 0, "maxLines": 0}
    for path in sorted(root.rglob("*.lean")):
        name = path.relative_to(root)
        if any(part in {".git", ".lake"} for part in name.parts):
            continue
        if path.is_symlink():
            problems["symlinks"].append(str(name))
            continue
        if not path.is_file():
            continue
        raw = path.read_bytes().decode("utf-8").replace("\r\n", "\n")
        lines = raw.count("\n") + int(bool(raw) and not raw.endswith("\n"))
        counts["files"] += 1
        counts["maxLines"] = max(counts["maxLines"], lines)
        if lines > 10_000:
            problems["overLength"].append(str(name))
        code = masked(raw)
        first = re.search(r"\S+", code)
        if first and first[0] == "module" and "/-!" not in raw[:first.start()]:
            counts["withModule"] += 1
        elif path.name != "lakefile.lean":
            problems["missingModule"].append(str(name))
    return {**counts, **problems}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument("--json", action="store_true", help="Include all affected file paths")
    opts = p.parse_args()
    report = scan(opts.root)
    if opts.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"{report['withModule']}/{report['files']} module headers; {len(report['overLength'])} files over 10,000 lines; "
              f"{len(report['symlinks'])} Lean symlinks; longest file {report['maxLines']} lines.")
    raise SystemExit(int(any(report[k] for k in ("missingModule", "overLength", "symlinks"))))
