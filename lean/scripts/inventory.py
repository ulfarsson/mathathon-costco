#!/usr/bin/env python3
"""List source-level Lean declarations and their project-local source lines."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
source = root / "OrderedRemoval" / "Statements.lean"
rows = []
namespaces = []
pat = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+([A-Za-z0-9_'.]+)")
for number, line in enumerate(source.read_text().splitlines(), 1):
    if line.startswith("namespace "):
        namespaces.append(line.split()[1])
    elif line.startswith("end ") and namespaces and line.split()[1] == namespaces[-1]:
        namespaces.pop()
    match = pat.match(line)
    if match:
        name = ".".join(namespaces + [match.group(2)])
        rows.append((name, match.group(1), number))
with (root / "results" / "declaration-index.tsv").open("w") as out:
    out.write("declaration\tkind\tline\n")
    for name, kind, number in rows:
        out.write(f"{name}\t{kind}\t{number}\n")
print(f"{len(rows)} source declarations indexed")
