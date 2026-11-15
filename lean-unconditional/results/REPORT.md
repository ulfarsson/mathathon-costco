# Verification, provenance, and declaration report

## Verdict

The infinite-family result is **Lean-verified and unconditional** under the final Lean 4.35.0 / Mathlib 4.35.0 pins. `OrderedRemoval/Unconditional.lean` proves OpenAI's 66×66 pattern is a `NoZeroLine` pattern outside `PolyRemoval`, instantiates the frozen family construction at that pattern, and packages the result as the requested existential injective sequence.

No compiled proof module contains a `sorry` declaration, `native_decide`, `admit`, `opaque`, or a custom axiom. The word `sorry` remains only in a stale introductory comment in the frozen `Statements.lean`, and in reference-only original attachments; neither is a proof dependency. The official comparator challenge was used for statement comparison but is not imported or delivered as a proof module because its challenge proof is a `sorry` placeholder.

### Final build and axiom results

```text
./scripts/verify.sh                   exit 0
lake build                            exit 0
Build completed successfully (9114 jobs).
AUDIT_DECL_COUNT 1803
AUDIT_BAD_COUNT 0
```

The audit enumerates every environment declaration in `OrderedRemoval.Statements`, `OrderedRemoval.Unconditional`, and all 61 OAI MatrixRemoval modules. This includes source declarations and generated auxiliary declarations. Its axiom-set totals are:

```text
AUDIT_SET [] count=117
AUDIT_SET [propext, Classical.choice, Quot.sound] count=877
AUDIT_SET [Quot.sound] count=33
AUDIT_SET [propext, Quot.sound] count=509
AUDIT_SET [propext] count=267
```

The eight new bridge theorems and `OAI.Problem348.no_polynomial_removal_bound` also have explicit `#print axioms` lines in `OrderedRemoval/Unconditional.lean`; every output is exactly `[propext, Classical.choice, Quot.sound]`.

## Required results

```lean
theorem OrderedRemoval.oai_not_polyRemoval :
    ¬ PolyRemoval (OAI.Problem348.fixedH : BMat 66 66)

theorem OrderedRemoval.oai_noZeroLine :
    NoZeroLine (OAI.Problem348.fixedH : BMat 66 66)

theorem OrderedRemoval.infinitely_many_counterexamples :
    ∃ f : ℕ → Pattern, Function.Injective f ∧
      ∀ t, NoZeroLine (f t).2 ∧ ¬ PolyRemoval (f t).2
```

`OrderedRemoval.oai_infinite_family` is the direct instantiation

```lean
infinite_family_of_counterexample
  (OAI.Problem348.fixedH : BMat 66 66) oai_noZeroLine oai_not_polyRemoval
```

and therefore gives injectivity of `paddingFamily fixedH`, infinitude of its range, the two counterexample properties for every `padding fixedH t`, and dimensions `(66+t, 66+t)`. No conditional counterexample hypothesis remains in any of these conclusions.

## OpenAI provenance and exact statement comparison

| Item | Record |
|---|---|
| Repository | <https://github.com/openai/math> |
| Commit | `4eaee87548250b2682affda7d05d947c05554bae` |
| Commit timestamp | `2026-10-29T17:35:35-07:00` |
| Official statement | `lean/ComparatorChallenges/MatrixRemoval.lean` |
| Proved theorem | `lean/OAI/Combinatorics/MatrixRemoval/Main.lean` |
| Original Lean | `v4.34.1` |
| Original Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Delivered Lean | `v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Delivered Mathlib | `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| License | Apache License 2.0, unchanged; SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |

All **61** files under `OAI/Combinatorics/MatrixRemoval/` are byte-identical to that OpenAI commit. The transitive-local-import script agrees that these 61 files are exactly the dependencies of `Main.lean`: there are no missing or unused MatrixRemoval files, and their only external import is `Mathlib`.

The comparison against the official challenge was separate from the file-for-file provenance diff:

- The definitions block from `BinaryMatrix` through `fixedDistance` in `Model.lean` is textually identical to the official file's definitions block.
- The complete statement text of `no_polynomial_removal_bound` in `Main.lean` is identical to the official statement through `:= by`; its SHA-256 is `7c4ea8b0abc19c85d41767edce1a8c61a9359e032a66cfbd8fc80e5330af54a5`.
- The official reference file's SHA-256 at that commit is `1db0fac5a4ddc57a90e9950cfd4e7e4e1681b4c8ce755e6ba5c169f3656b77e9`.

**Porting differences: none.** No definition, statement, proof, or import in the 61-file proof closure was edited. In particular, there are no renamed OpenAI declarations and no compatibility wrappers hiding a changed statement. The only new Lean code is the separate OrderedRemoval bridge, the project root aggregators, and the axiom-audit instrumentation.

The comparator challenge itself is not part of that 61-file closure. It redeclares the same `OAI.Problem348` names and retains a `sorry` proof, so importing it together with the real proof would both duplicate declarations and risk `sorryAx`. After performing the byte and statement comparisons above, it was excluded from the delivered proof tree. This exclusion is not a change to any vendored OpenAI proof file.

`LICENSE.openai` and the retained duplicate `OAI_LICENSE` are both byte-identical to OpenAI's `LICENSE`. Attribution and the original revision are also recorded in `README.md`, `openai-source-audit.log`, and every row of the OAI portion of `new-declaration-index.tsv`.

## New declaration-to-claim map

The following eight declarations are the new mathematical bridge in `OrderedRemoval/Unconditional.lean`. None has an upstream original; each is additional code, not an OpenAI source edit.

| Declaration | Claim it supports | Difference from OpenAI's files |
|---|---|---|
| `OrderedRemoval.oai_hamming_eq` | OAI `hammingDistance A B` equals frozen `hamming A B`; proved by `rfl`. | New bridge lemma; no upstream change. |
| `OrderedRemoval.oai_copyCount_eq` | For square `H`, OAI's count over pairs of bundled `IncreasingMap`s equals frozen `copyCount` over plain map pairs satisfying `IsCopy`. The explicit subtype equivalence preserves both strict monotonicity proofs and the entry-match condition. | New bridge lemma; no upstream change. |
| `OrderedRemoval.oai_HFree_iff` | For `fixedH`, OAI `HFree` is equivalent to frozen `Free`, via copy-count equality and `copyCount_eq_zero_iff`. | New bridge lemma; no upstream change. |
| `OrderedRemoval.oai_noZeroLine` | Every one of the 66 rows and 66 columns of the literal `fixedH` contains `true`, by finite `fin_cases` and kernel `decide`. | New required result; uses unchanged `fixedH`. |
| `OrderedRemoval.oai_fixedMinEdits_eq_editDist` | OAI's finite `min'` definition of `fixedMinEdits` equals frozen `editDist` at `fixedH`. | New bridge lemma; handles the sentinel explicitly. |
| `OrderedRemoval.oai_not_polyRemoval` | The required `¬ PolyRemoval fixedH`, obtained by transporting all quantitative bounds and contradicting a hypothetical frozen polynomial-removal bound. | New required result; theorem statement and conclusion are not present in OpenAI's different API. |
| `OrderedRemoval.infinitely_many_counterexamples` | The exact requested existential injective sequence of `NoZeroLine`, non-`PolyRemoval` patterns; obtained by dropping the size conjunct from `exists_injective_counterexample_family`. | New unconditional consequence. |
| `OrderedRemoval.oai_infinite_family` | The full four-part frozen `infinite_family_of_counterexample` result instantiated at `fixedH`. | New explicit instantiation. |

The **611 unchanged OAI source declarations** are indexed individually in `new-declaration-index.tsv` (450 theorems, 129 definitions, 24 abbreviations, seven structures, and one inductive type). Each row gives its fully qualified source name, kind, file, line, supporting role, and the same provenance entry: `none; byte-identical to openai/math@4eaee875…`. Together with the eight bridge rows, that index contains **619 declarations**. The two top-level OAI declarations have specific roles:

- `OAI.Problem348.no_polynomial_removal_bound`: the official quantitative result used by `oai_not_polyRemoval`;
- `OAI.Problem348.counterexample_sequence`: the explicit host sequence from which that bound is assembled.

All other OAI rows are marked as internal declarations in this theorem's transitive proof closure, or as statement/definition components when they occur in `Model.lean`. The environment-level axiom audit, rather than the textual inventory, additionally covers compiler-generated declarations.

## Why the bridge is valid

1. **The carriers agree definitionally.** `OAI.Problem348.BinaryMatrix n` and `BMat n n` both reduce to `Fin n → Fin n → Bool`; no matrix transport or entrywise bijection is needed.
2. **The Hamming distances and copy counts agree.** Hamming equality is definitional. Copy-count equality is `Fintype.card_congr` across the equivalence between bundled monotone maps and plain maps carrying the same monotonicity proofs.
3. **Freeness agrees.** Both predicates characterize the absence of an ordered copy, one through cardinality zero and one through the negated existential.
4. **Minimal edits equal edit distance.** For the upper bound, `editDist_spec` supplies a free matrix attaining `editDist`, whose Hamming distance occurs in OAI's finite image. For the reverse bound, inspect a `min'` witness. If it is free, `editDist_le` applies. If not, the minimum is the sentinel `n*n+1`; but `editDist_le_card` gives `editDist ≤ n*n`, since `fixedH` has a `true` entry and hence a free zero-matrix comparison. The sentinel case is therefore impossible.
5. **The real bounds transport in the right direction.** OAI gives `fixedDistance A ≥ ε` and `n ≥ 1`. Positivity of `(n : ℝ)^2` yields `ε*n² ≤ fixedMinEdits A = editDist fixedH A`. OAI's `ε < 1` supplies frozen `ε ≤ 1`. Copy-count equality and `66+66 = 132` turn OAI's strict upper bound into exactly the contradiction required by frozen `PolyRemoval`; `Real.rpow ε C` is the same operation denoted `ε ^ C` in both statements.
6. **The family is frozen code.** `oai_noZeroLine` and `oai_not_polyRemoval` discharge all premises of the existing family construction. No probabilistic or analytic re-proof is introduced in the bridge.

Three independently written bridge candidates were compiled and reviewed during development. The delivered module integrates one minimization argument; an independent candidate also checked the route through `counterexample_sequence` directly. Neither alternate development is included in the package or required by its proofs.

## Frozen statements and prior repairs

`OrderedRemoval/Statements.lean` was not edited in this task. Its SHA-256 is

```text
b2625ddfcff3d792375faa0ed3f05f3ee15c7e83b4ec7755825c40438082c5d4
```

which is byte-identical to the file in `results/ordered-removal-lean4.35.0.zip` before this update. The earlier statement-preservation evidence remains in `statement-preservation-final.log`; the original 304-declaration inventory remains in `declaration-index.tsv`.

For completeness, the preceding package already contained three statement repairs relative to the raw attachment: `editDist_eq_zero_iff` adds free-host existence, and `editDist_blockDiag_one` / `editDist_blockDiag` add `0 < k`. **These are pre-existing changes, not changes made or newly authorized by this task.** This report does not rely on the earlier report's unsupported attribution of their authorization.

The degenerate counterexamples to the unrepaired claims are preserved and were recompiled under the delivered pins:

- `no_section2_editDist_eq_zero_iff`;
- `no_editDist_blockDiag_one`;
- `no_editDist_blockDiag`.

Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`; see `counterexample-verification.log`. The two non-fatal warnings in that log are unused-variable linters in the earlier certificate, not proof gaps.

## Dependency pins and reproducibility

| Dependency | Revision |
|---|---|
| Lean | `v4.35.0` / `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

`lakefile.toml` pins the direct Mathlib revision; `lake-manifest.json` fixes every transitive revision; `lean-toolchain` fixes Lean. The OpenAI source is pinned separately by the full commit above.

### Clean-clone check

A throwaway local Git repository was staged outside the deliverable and cloned with `git clone --no-hardlinks`. No commit or remote operation was performed on the user's root repository. Before verification the clone had no `.lake/build`. It then ran the delivered `./scripts/verify.sh`, which installed the official pinned toolchain, materialized exactly the pinned dependencies and cache, and built from source.

```text
CLEAN_CLONE_HEAD 0f04aad582308a77bf57c35ed800b342ac85710f
CLEAN_CLONE_BUILD_ARTIFACTS_BEFORE absent
CLEAN_CLONE_VERIFY_EXIT 0
AUDIT_DECL_COUNT 1803
AUDIT_BAD_COUNT 0
Build completed successfully (9114 jobs).
```

The delivered source set has 66 Lean files: 61 OAI modules, `Statements.lean`, `Unconditional.lean`, `Audit.lean`, and the two root aggregators. The clean-clone check covered the final Lean proof sources and verifier; later report/index additions do not enter any import or build command.

## Evidence files

- `ordered-removal-lean4.35.0.zip`: updated source package.
- `clean-clone-build.log`: full clean-clone verifier output and live audit.
- `verify-script.log`: independent invocation of the delivered root verifier.
- `lake-build-final.log`: independent root `lake build` output.
- `axiom-audit-final.log`: every `AUDIT_DECL` line and every explicit `#print axioms` result from the root build.
- `openai-source-audit.log`: exact commit, import-closure, source-diff, statement-comparison, license, and frozen-file checks.
- `openai-source-manifest.sha256`: hashes of all 61 vendored files, the OpenAI license, bridge, and frozen statements.
- `new-declaration-index.tsv`: all 611 OAI and eight bridge declarations, with claims and differences.
- `declaration-index.tsv`: original 304-declaration source index.
- `statement-changes.json`, `statement-preservation-final.log`: earlier statement repair and preservation evidence.
- `counterexample-verification.log`: fresh compilation of all three original-statement refutations.
