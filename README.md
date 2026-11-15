# mathathon-costco
Repo for the 2026 Mathathon

## Lean (v4.35.0, Mathlib v4.35.0)

- `lean/`: our proof. Any counterexample with no all-zero row or column gives
  infinitely many (`OrderedRemoval/Statements.lean`).
- `lean-unconditional/`: the same proof combined with OpenAI's Lean proof of their
  66×66 counterexample (Apache-2.0, see `LICENSE.openai`), so the infinite family is
  proved outright (`OrderedRemoval/Unconditional.lean`).
- Both folders also contain the duplication theorem (`OrderedRemoval/Dup/`): `H` satisfies
  the conjecture if and only if `red(H)` does (`polyRemoval_iff_red` in `Dup/Red.lean`). In
  `lean-unconditional/`, `Dup/Unconditional.lean` adds that OpenAI's pattern is reduced, so
  repeating any of its rows or columns gives another counterexample
  (`oai_infl_not_polyRemoval`).

Build either one with `lake exe cache get && lake build` inside its folder.
