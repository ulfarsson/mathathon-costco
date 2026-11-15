# Ordered removal: direct sums and infinite counterexample families

This project formalizes ordered-removal edit distance and copy counts, the direct-sum and zero-column constructions, their counterexample corollaries, and an explicit infinite family of counterexamples obtained by iterating the `(1)` block.

## Build and verification

Toolchain: **Lean 4.35.0** (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), **Mathlib 4.35.0** (`56a005855ea17e0b0958f73ec801ae140b0a1679`). All transitive dependency commits are recorded in `lake-manifest.json`.

Run:

```bash
./scripts/verify.sh
```

Or, with elan installed:

```bash
elan toolchain install leanprover/lean4:v4.35.0
elan run leanprover/lean4:v4.35.0 lake exe cache get
elan run leanprover/lean4:v4.35.0 lake build
```

The script uses the installed elan toolchain when available and otherwise fetches the official release tarball into `.scratch`. It never upgrades a dependency. `lake build` compiles `OrderedRemoval.Statements` and `OrderedRemoval.Audit`, which fails if any declaration depends on an axiom outside `{propext, Classical.choice, Quot.sound}`.

Main module: [`OrderedRemoval/Statements.lean`](OrderedRemoval/Statements.lean). Detailed report: [`results/REPORT.md`](results/REPORT.md).
