"""Locate named Lean declarations in this edition without running a toolchain."""

from collections import defaultdict
import os
from pathlib import Path
import re


IDENT = r"(?:«[^»\n]+»|[\w][\w'!?]*)(?:\.(?:«[^»\n]+»|[\w][\w'!?]*))*"
MODIFIERS = r"(?:(?:public|private|protected|noncomputable|nonrec|unsafe|partial|meta|scoped|local)[ \t]+)*"
SCOPE = re.compile(MODIFIERS + r"(namespace|section|mutual|end)\b(?:[ \t]+(" + IDENT + r"))?")
DECLARATION = re.compile(
    r"(?:@\[[^\n]*?\][ \t]*)*" + MODIFIERS
    + r"(?:theorem|lemma|def|irreducible_def|abbrev|structure|class|inductive|instance|opaque|axiom)"
    + r"[ \t]+(" + IDENT + r")"
)


def masked(source):
    """Keep line and character offsets while removing strings and nested comments."""
    chars = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if not depth and not string and pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            chars[i:end] = " " * (end - i)
            i = end
            continue
        if not string and pair == "/-":
            depth += 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if depth and pair == "-/":
            depth -= 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if not depth and source[i] == '"':
            string = not string
            chars[i] = " "
        elif string and source[i] == "\\" and i + 1 < len(chars):
            chars[i:i + 2] = [" ", "\n" if source[i + 1] == "\n" else " "]
            i += 2
            continue
        elif (depth or string) and source[i] != "\n":
            chars[i] = " "
        i += 1
    return "".join(chars)


def declarations(source):
    """Yield the fully qualified name and one-based line of each named command."""
    scopes = []
    for line_number, raw in enumerate(masked(source).splitlines(), 1):
        line = raw.lstrip()
        scope = SCOPE.match(line)
        if scope:
            kind, name = scope.groups()
            if kind == "end":
                if scopes:
                    scopes.pop()
            else:
                scopes.append(name if kind == "namespace" else None)
            continue
        command = DECLARATION.match(line)
        if command:
            name = command[1]
            if name.startswith("_root_."):
                name = name.removeprefix("_root_.")
            else:
                name = ".".join([*(scope for scope in scopes if scope), name])
            yield name, line_number


def unique_locations(sources, wanted):
    """A link must have exactly one definition among the supplied source files."""
    locations = defaultdict(list)
    for path, content in sources:
        for name, number in declarations(content):
            if name in wanted:
                locations[name].append(f"{path}#L{number}")
    return {name: rows[0] for name, rows in sorted(locations.items()) if len(rows) == 1}


def project_sources(root):
    """Avoid traversing downloaded toolchains and Lake build directories."""
    for directory in ("Lean", "bounded", "picard", "Comparison"):
        for base, directories, names in os.walk(root / directory):
            directories[:] = sorted(d for d in directories if not d.startswith("."))
            for name in sorted(names):
                if name.endswith(".lean"):
                    yield Path(base) / name
