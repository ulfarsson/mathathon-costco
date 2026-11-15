#!/usr/bin/env python3
"""Index the vendored OAI declarations and the new OrderedRemoval bridge."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
OPENAI_REV = "4eaee87548250b2682affda7d05d947c05554bae"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:{(]+)"
)
BRIDGE_CLAIMS = {
    "oai_hamming_eq": "OpenAI hammingDistance is the frozen hamming distance.",
    "oai_copyCount_eq": "OpenAI and frozen ordered-copy counts agree for square patterns.",
    "oai_HFree_iff": "OpenAI HFree and frozen Free agree for fixedH hosts.",
    "oai_noZeroLine": "Every row and column of fixedH contains true.",
    "oai_fixedMinEdits_eq_editDist": "OpenAI fixedMinEdits equals frozen editDist for fixedH.",
    "oai_not_polyRemoval": "fixedH does not satisfy frozen PolyRemoval.",
    "infinitely_many_counterexamples": "There is an injective family of NoZeroLine non-PolyRemoval patterns.",
    "oai_infinite_family": "The frozen infinite_family_of_counterexample instantiated at fixedH.",
}


def declarations(source: Path):
    namespaces = []
    for number, line in enumerate(source.read_text().splitlines(), 1):
        if line.startswith("namespace "):
            namespaces.append(line.split()[1])
            continue
        if line.startswith("end ") and namespaces:
            end_name = line.split()[1]
            current = namespaces[-1]
            if current == end_name or current.endswith("." + end_name):
                namespaces.pop()
            continue
        match = DECL.match(line)
        if match:
            local_name = match.group(2)
            full_name = ".".join(namespaces + [local_name])
            yield full_name, match.group(1), number


rows = []
for source in sorted((ROOT / "OAI/Combinatorics/MatrixRemoval").glob("*.lean")):
    relative = source.relative_to(ROOT).as_posix()
    for name, kind, number in declarations(source):
        if name == "OAI.Problem348.no_polynomial_removal_bound":
            claim = "OpenAI's official non-polynomial-removal bound; source of oai_not_polyRemoval."
        elif name == "OAI.Problem348.counterexample_sequence":
            claim = "Explicit host sequence from which OpenAI's non-polynomial-removal bound is assembled."
        elif relative.endswith("/Model.lean"):
            claim = "Statement/definition component of OpenAI's fixedH, copy count, or edit-distance formalization."
        else:
            claim = "Internal declaration in the transitive proof closure of no_polynomial_removal_bound."
        rows.append((name, kind, relative, number, claim,
                     f"none; byte-identical to openai/math@{OPENAI_REV}"))

bridge = ROOT / "OrderedRemoval/Unconditional.lean"
for name, kind, number in declarations(bridge):
    local_name = name.removeprefix("OrderedRemoval.")
    rows.append((name, kind, "OrderedRemoval/Unconditional.lean", number,
                 BRIDGE_CLAIMS[local_name], "new bridge declaration; no upstream original"))

output = ROOT / "results/new-declaration-index.tsv"
with output.open("w") as out:
    out.write("declaration\tkind\tsource\tline\tclaim_support\tdifference_from_openai\n")
    for row in rows:
        out.write("\t".join(map(str, row)) + "\n")
print(f"NEW_DECLARATION_INDEX_COUNT {len(rows)}")
print(f"OPENAI_SOURCE_DECL_COUNT {len(rows) - len(BRIDGE_CLAIMS)}")
print(f"BRIDGE_DECL_COUNT {len(BRIDGE_CLAIMS)}")
if len(rows) - len(BRIDGE_CLAIMS) != 611:
    raise SystemExit("expected 611 OAI source declarations; inspect the parser")
