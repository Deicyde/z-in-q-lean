"""Check every preview header and import list with Lean and Palomar's source scanner."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys


def parsed(lean, root, paths):
    result = {}
    for start in range(0, len(paths), 64):
        batch = paths[start:start + 64]
        raw = subprocess.check_output([lean, "--deps-json", *(root / p for p in batch)])
        results = json.loads(raw)["imports"]
        if len(results) != len(batch):
            raise ValueError("Lean returned an incomplete list of headers")
        for path, item in zip(batch, results):
            if item["errors"]:
                raise ValueError(f"{path}: {item['errors']}")
            result[path] = item["result"]
    return result


def digest_tree(root, paths):
    digest = sha256()
    for name in paths:
        digest.update(name.encode() + b"\0" + sha256((root / name).read_bytes()).digest())
    return digest.hexdigest()


def check(verifier, lean, before, after):
    revision = subprocess.check_output(["git", "-C", verifier, "rev-parse", "HEAD"], text=True).strip()
    if revision != "14aa8d6b3c2f14a8540605e37144560b9a00e7e7":
        raise ValueError("Use the pinned PalomarSubmission revision")
    subprocess.run(["git", "-C", verifier, "diff", "--exit-code", "HEAD", "--", "scripts"], check=True)
    sys.path.insert(0, str(verifier))
    from scripts.source_requirements import inspect_lean_sources, lean_source_files

    paths = sorted(p.relative_to(before).as_posix() for p in lean_source_files(before))
    if paths != sorted(p.relative_to(after).as_posix() for p in lean_source_files(after)):
        raise ValueError("The editions contain different source paths")
    report, issues = inspect_lean_sources(after)
    if not paths or issues:
        raise ValueError(f"Palomar source check: {len(paths)} files, {issues[:3]}")
    original, preview = parsed(lean, before, paths), parsed(lean, after, paths)
    for path in paths:
        if not preview[path]["isModule"] or preview[path]["imports"] != original[path]["imports"]:
            raise ValueError(f"The header or the imported modules changed in {path}")
    return {
        "lean": subprocess.check_output([lean, "--version"], text=True).strip(),
        "sourceVerifier": revision, "inventory": report,
        "editionLeanSHA256": digest_tree(before, paths), "previewLeanSHA256": digest_tree(after, paths),
        "originalModuleHeaders": sum(row["isModule"] for row in original.values()),
        "previewModuleHeaders": len(paths), "identicalImportLists": len(paths),
        "scope": "Lean parsed the headers and Palomar checked the source files. Proof bodies were not elaborated by this check.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("verifier", "lean", "edition", "preview"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    result = check(args.verifier.resolve(), args.lean.absolute(), args.edition.resolve(), args.preview.resolve())
    print(json.dumps(result, indent=2))
