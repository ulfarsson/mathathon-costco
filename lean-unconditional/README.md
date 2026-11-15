# Ordered removal: unconditional infinite counterexample families

This project formalizes ordered-removal edit distance and copy counts, the direct-sum and zero-column constructions, and their counterexample corollaries. It combines the frozen `OrderedRemoval` development with OpenAI's proved 66×66 obstruction to obtain an **unconditional** injective infinite family of `NoZeroLine` patterns that do not satisfy `PolyRemoval`.

## Build and verification

Toolchain: **Lean 4.35.0** (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), **Mathlib 4.35.0** (`56a005855ea17e0b0958f73ec801ae140b0a1679`). Every transitive dependency revision is fixed in `lake-manifest.json`.

```bash
./scripts/verify.sh
```

The script uses the pinned elan toolchain when available and otherwise downloads the official Lean 4.35.0 release into `.scratch`. It fetches the pinned Mathlib cache and runs `lake build`; it never upgrades a dependency.

The default build compiles:

- `OrderedRemoval/Statements.lean`, unchanged from the preceding package;
- `OrderedRemoval/Unconditional.lean`, the new eight-declaration bridge;
- all 61 modules in the transitive local-import closure of `OAI.Combinatorics.MatrixRemoval.Main`;
- `OrderedRemoval/Audit.lean`, which computes the axioms of every declaration in those 63 modules and fails on anything outside `{propext, Classical.choice, Quot.sound}`.

The clean-clone source set contains 66 Lean files: 61 vendored OAI modules, three `OrderedRemoval` modules, and the root `OAI.lean` and `OrderedRemoval.lean` aggregators. Verification completed 9,114 jobs and reported:

```text
AUDIT_DECL_COUNT 1803
AUDIT_BAD_COUNT 0
Build completed successfully (9114 jobs).
```

## Main results

[`OrderedRemoval/Unconditional.lean`](OrderedRemoval/Unconditional.lean) proves:

- `OrderedRemoval.oai_not_polyRemoval : ¬ PolyRemoval (OAI.Problem348.fixedH : BMat 66 66)`;
- `OrderedRemoval.oai_noZeroLine : NoZeroLine (OAI.Problem348.fixedH : BMat 66 66)`;
- `OrderedRemoval.infinitely_many_counterexamples`, the required existential injective family;
- `OrderedRemoval.oai_infinite_family`, the explicit `infinite_family_of_counterexample` instantiation at `fixedH`.

The bridge also proves that the two Hamming distances, copy counts, freeness predicates, and minimal-edit distances agree. No `sorry`, `native_decide`, custom axiom, or challenge placeholder occurs in the compiled proof modules.

## OpenAI source and attribution

- **Repository:** <https://github.com/openai/math>
- **Recorded commit:** `4eaee87548250b2682affda7d05d947c05554bae` (`2026-10-29T17:35:35-07:00`)
- **Original statement:** `lean/ComparatorChallenges/MatrixRemoval.lean`, theorem `OAI.Problem348.no_polynomial_removal_bound`
- **Proof:** `lean/OAI/Combinatorics/MatrixRemoval/Main.lean` and its transitive local imports, vendored under [`OAI/Combinatorics/MatrixRemoval`](OAI/Combinatorics/MatrixRemoval)
- **Original pins:** Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- **Porting result:** all 61 proof files are byte-identical to that commit; no definitions, statements, proofs, or imports required editing for Lean/Mathlib 4.35.0
- **License:** Apache License 2.0, copied unchanged to [`LICENSE.openai`](LICENSE.openai) (and retained as `OAI_LICENSE`)

The official definitions block and theorem statement were separately compared with the vendored `Model.lean` and `Main.lean`, respectively. Both comparisons passed. The challenge file itself has a `sorry` placeholder and redeclares the proof's names, so it is reference-only and is intentionally not part of the delivered proof tree or import closure.

See [`results/REPORT.md`](results/REPORT.md), [`results/new-declaration-index.tsv`](results/new-declaration-index.tsv), and [`results/openai-source-audit.log`](results/openai-source-audit.log) for the complete provenance, claim map, porting differences, and verification evidence.
