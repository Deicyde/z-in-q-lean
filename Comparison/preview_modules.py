"""Prepare a separate Lean source tree for testing migration to the module system."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "dashboard"))
from lean_source import masked


def convert(source):
    """Preserve the imported modules, ordinary header comments and proof bodies."""
    lines = source.splitlines(keepends=True)
    imports = []
    for number, line in enumerate(masked(source).splitlines()):
        if not line.strip():
            continue
        if not re.fullmatch(r"[ \t]*import(?:[ \t]+[\w.]+)+[ \t]*", line):
            break
        start = re.match(r"[ \t]*", line).end()
        lines[number] = lines[number][:start] + "public " + lines[number][start:]
        imports.append(number)
    if not imports:
        raise ValueError("Unrecognized imports")
    first, last = imports[0], imports[-1]
    return ("".join(lines[:first]) + "module\n\n" + "".join(lines[first:last + 1])
            + "\n@[expose] public section\n" + "".join(lines[last + 1:]))


def prepare(edition, output):
    if output.exists() or output.is_relative_to(edition):
        raise ValueError("Choose a new directory outside the edition")
    record = json.loads((edition / "Comparison/repository-inventory.json").read_text())
    accepted = set(record["moduleFiles"])
    paths = sorted((p for p in edition.rglob("*.lean")
                    if not {".git", ".lake"}.intersection(p.relative_to(edition).parts)),
                   key=lambda p: p.relative_to(edition).as_posix())
    if len(paths) != record["inventory"]["files_checked"]:
        raise ValueError("The source file count differs from the audited inventory")
    digest = sha256()
    with TemporaryDirectory(dir=output.parent) as scratch:
        stage = Path(scratch) / "sources"
        for path in paths:
            name = path.relative_to(edition).as_posix()
            if path.is_symlink():
                raise ValueError(f"Expected a regular source file: {name}")
            data = path.read_bytes()
            digest.update(name.encode() + b"\0" + sha256(data).digest())
            if name not in accepted:
                data = convert(data.decode()).encode()
            target = stage / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        if digest.hexdigest() != record["leanSourceSHA256"]:
            raise ValueError("The input Lean sources differ from the audited edition")
        stage.rename(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("edition", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    prepare(args.edition.resolve(), args.output.resolve())
