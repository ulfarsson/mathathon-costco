/-
§2 sanity lemmas of `Statements.lean` (namespace `OrderedRemoval`), proven.

Self-contained: §1 definitions are copied verbatim from the frozen file, then the
five §2 theorems are proved.

IMPORTANT FINDING (machine-checked at the bottom of this file):
`editDist_eq_zero_iff` is FALSE as stated for degenerate patterns with an empty
row/column set (e.g. `H : BMat 0 1`): then every matrix contains `H`, so the set
of distances to `H`-free matrices is empty, `sInf ∅ = 0`, while `Free H A` is
false.  We prove the statement in the form that is actually true and used
downstream (hypothesis: some `H`-free matrix exists, which holds automatically
under `NoZeroLine H` via `free_zero`), and give the refutation of the literal
statement.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OrderedRemoval

open Classical

/-! ## 1. Definitions (verbatim from Statements.lean) -/

abbrev BMat (a b : ℕ) := Fin a → Fin b → Bool

def IsCopy {k l n m : ℕ} (H : BMat k l) (A : BMat n m) (r : Fin k → Fin n) (c : Fin l → Fin m) :
    Prop :=
  StrictMono r ∧ StrictMono c ∧ ∀ i j, A (r i) (c j) = H i j

def Contains {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ∃ r c, IsCopy H A r c

def Free {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ¬ Contains H A

noncomputable def copyCount {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=
  (Finset.univ.filter
    (fun rc : (Fin k → Fin n) × (Fin l → Fin m) => IsCopy H A rc.1 rc.2)).card

noncomputable def hamming {n m : ℕ} (A B : BMat n m) : ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2)).card

noncomputable def editDist {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=
  sInf {d | ∃ B : BMat n m, Free H B ∧ hamming A B = d}

def ones (a b : ℕ) : BMat a b := fun _ _ => true

def zeros (a b : ℕ) : BMat a b := fun _ _ => false

def NoZeroLine {k l : ℕ} (H : BMat k l) : Prop :=
  (∀ i, ∃ j, H i j = true) ∧ (∀ j, ∃ i, H i j = true)

/-! ## 2. Sanity lemmas -/

/-- A pattern with a `1` is absent from the zero matrix. -/
theorem free_zero {k l n m : ℕ} (H : BMat k l) (h : ∃ i j, H i j = true) :
    Free H (zeros n m) := by
  rintro ⟨r, c, -, -, hrc⟩
  obtain ⟨i, j, hij⟩ := h
  have h1 : H i j = false := by
    rw [← hrc i j]
    rfl
  rw [h1] at hij
  exact Bool.noConfusion hij

/-- `editDist` is attained by an `H`-free matrix, when one exists. -/
theorem editDist_spec {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (h : ∃ B : BMat n m, Free H B) :
    ∃ B : BMat n m, Free H B ∧ hamming A B = editDist H A := by
  obtain ⟨B₀, hB₀⟩ := h
  have hne : {d : ℕ | ∃ B : BMat n m, Free H B ∧ hamming A B = d}.Nonempty :=
    ⟨hamming A B₀, B₀, hB₀, rfl⟩
  exact Nat.sInf_mem hne

/-- `editDist` is at most the distance to any `H`-free matrix. -/
theorem editDist_le {k l n m : ℕ} (H : BMat k l) (A B : BMat n m) (hB : Free H B) :
    editDist H A ≤ hamming A B :=
  Nat.sInf_le ⟨B, hB, rfl⟩

/-- The Hamming distance is zero exactly for equal matrices. -/
theorem hamming_eq_zero_iff {n m : ℕ} (A B : BMat n m) : hamming A B = 0 ↔ A = B := by
  constructor
  · intro h
    funext i j
    by_contra hne
    have hmem : (i, j) ∈ Finset.univ.filter (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2) := by
      simp [hne]
    have hpos : 0 < (Finset.univ.filter
        (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2)).card :=
      Finset.card_pos.mpr ⟨(i, j), hmem⟩
    unfold hamming at h
    omega
  · rintro rfl
    simp [hamming]

/-- The Hamming distance from a matrix to itself is zero. -/
theorem hamming_self {n m : ℕ} (A : BMat n m) : hamming A A = 0 := by
  simp [hamming]

/-- `copyCount H A = 0` exactly when `A` is `H`-free. -/
theorem copyCount_eq_zero_iff {k l n m : ℕ} (H : BMat k l) (A : BMat n m) :
    copyCount H A = 0 ↔ Free H A := by
  constructor
  · intro h
    rintro ⟨r, c, hrc⟩
    have hmem : (r, c) ∈ Finset.univ.filter
        (fun rc : (Fin k → Fin n) × (Fin l → Fin m) => IsCopy H A rc.1 rc.2) := by
      simp [hrc]
    have hpos := Finset.card_pos.mpr ⟨(r, c), hmem⟩
    unfold copyCount at h
    omega
  · intro h
    unfold copyCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact h ⟨x.1, x.2, hx⟩

/-- `editDist H A = 0` exactly when `A` is `H`-free, *provided* an `H`-free matrix
exists.  This hypothesis is required: without it the set whose `sInf` defines
`editDist` is empty and `editDist H A = 0` holds vacuously. -/
theorem editDist_eq_zero_iff_of_exists_free {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (hfree : ∃ B : BMat n m, Free H B) :
    editDist H A = 0 ↔ Free H A := by
  constructor
  · intro h0
    obtain ⟨B, hB, hd⟩ := editDist_spec H A hfree
    have hAB : A = B := (hamming_eq_zero_iff A B).mp (by rw [hd, h0])
    simpa [hAB] using hB
  · intro hA
    have h := editDist_le H A A hA
    rw [hamming_self] at h
    omega

/-- The form of `editDist_eq_zero_iff` used downstream: as soon as `H` has a `1`
(in particular for every nonempty pattern satisfying `NoZeroLine`), an `H`-free
matrix exists (`zeros`), so the unconditional statement holds. -/
theorem editDist_eq_zero_iff_of_exists_one {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (h : ∃ i j, H i j = true) :
    editDist H A = 0 ↔ Free H A :=
  editDist_eq_zero_iff_of_exists_free H A ⟨zeros n m, free_zero H h⟩


/-- Unconditional version of the frozen statement: it fails exactly when there is
no `H`-free matrix at all, in which case the `sInf` is `0` for every `A`. -/
theorem editDist_eq_zero_iff_or {k l n m : ℕ} (H : BMat k l) (A : BMat n m) :
    editDist H A = 0 ↔ Free H A ∨ ¬ ∃ B : BMat n m, Free H B := by
  constructor
  · intro h0
    by_cases h : ∃ B : BMat n m, Free H B
    · exact Or.inl ((editDist_eq_zero_iff_of_exists_free H A h).mp h0)
    · exact Or.inr h
  · rintro (hA | hnone)
    · exact (editDist_eq_zero_iff_of_exists_free H A ⟨A, hA⟩).mpr hA
    · rw [editDist]
      have hS : {d : ℕ | ∃ B : BMat n m, Free H B ∧ hamming A B = d} = ∅ := by
        ext d
        constructor
        · rintro ⟨B, hB, -⟩
          exact hnone ⟨B, hB⟩
        · intro hd
          exact absurd hd (by simp)
      rw [hS, Nat.sInf_empty]

/-- Exact condition for the frozen statement to hold for all `A`. -/
theorem forall_editDist_eq_zero_iff_iff {k l n m : ℕ} (H : BMat k l) :
    (∀ A : BMat n m, editDist H A = 0 ↔ Free H A) ↔ ∃ B : BMat n m, Free H B := by
  constructor
  · intro h
    by_contra hnone
    have h0 : editDist H (zeros n m) = 0 := by
      rw [editDist]
      have hS : {d : ℕ | ∃ B : BMat n m, Free H B ∧ hamming (zeros n m) B = d} = ∅ := by
        ext d
        constructor
        · rintro ⟨B, hB, -⟩
          exact hnone ⟨B, hB⟩
        · intro hd
          exact absurd hd (by simp)
      rw [hS, Nat.sInf_empty]
    exact hnone ⟨zeros n m, (h (zeros n m)).mp h0⟩
  · rintro ⟨B, hB⟩ A
    exact editDist_eq_zero_iff_of_exists_free H A ⟨B, hB⟩

/-- For a nonempty pattern (`0 < k`, `0 < l`) an `H`-free matrix always exists:
if a strict monotone embedding of the pattern shape is impossible every matrix is
free, otherwise `ones` is free when `H` has a `0` and `zeros` when it has none. -/
theorem exists_free_of_pos {k l n m : ℕ} (H : BMat k l) (hk : 0 < k) (hl : 0 < l) :
    ∃ B : BMat n m, Free H B := by
  by_cases hkn : k ≤ n
  · by_cases hlm : l ≤ m
    · by_cases hz : ∃ i j, H i j = false
      · refine ⟨ones n m, ?_⟩
        rintro ⟨r, c, -, -, hrc⟩
        obtain ⟨i, j, hij⟩ := hz
        have h1 : H i j = true := by
          rw [← hrc i j]
          rfl
        rw [h1] at hij
        exact Bool.noConfusion hij
      · refine ⟨zeros n m, ?_⟩
        rintro ⟨r, c, -, -, hrc⟩
        have h1 : H (⟨0, hk⟩ : Fin k) (⟨0, hl⟩ : Fin l) = false := by
          rw [← hrc ⟨0, hk⟩ ⟨0, hl⟩]
          rfl
        exact hz ⟨⟨0, hk⟩, ⟨0, hl⟩, h1⟩
    · refine ⟨zeros n m, ?_⟩
      rintro ⟨r, c, -, hc, -⟩
      have hcard : l ≤ m := by
        have := Fintype.card_le_of_injective c hc.injective
        simpa using this
      omega
  · refine ⟨zeros n m, ?_⟩
    rintro ⟨r, c, hr, -, -⟩
    have hcard : k ≤ n := by
      have := Fintype.card_le_of_injective r hr.injective
      simpa using this
    omega

/-- Drop-in repaired §2 statement with the same positivity repair as §3/§5. -/
theorem editDist_eq_zero_iff_of_pos {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (hk : 0 < k) (hl : 0 < l) :
    editDist H A = 0 ↔ Free H A :=
  editDist_eq_zero_iff_of_exists_free H A (exists_free_of_pos H hk hl)

/-! ## Machine-checked refutation of the literal statement of `editDist_eq_zero_iff` -/

/-- For `H : BMat 0 1` every matrix contains `H` (the row condition is vacuous). -/
theorem contains_of_empty_rows {n m : ℕ} (l : ℕ) (hl : l ≤ m) (B : BMat n m) :
    Contains (fun (_ : Fin 0) (_ : Fin l) => false) B := by
  refine ⟨fun i => i.elim0, Fin.castLE hl, ?_, ?_, ?_⟩
  · intro a b hab
    exact absurd a.isLt (Nat.not_lt_zero a.val)
  · exact Fin.strictMono_castLE hl
  · intro i
    exact i.elim0

/-- The literal `editDist_eq_zero_iff` is false: for a pattern with no rows,
`editDist` is `0` (there is no `H`-free matrix at all) but `Free` is false. -/
theorem editDist_eq_zero_iff_counterexample :
    ¬ (editDist (fun (_ : Fin 0) (_ : Fin 1) => false) (zeros 1 1) = 0 ↔
        Free (fun (_ : Fin 0) (_ : Fin 1) => false) (zeros 1 1)) := by
  have hContains : ∀ B : BMat 1 1, Contains (fun (_ : Fin 0) (_ : Fin 1) => false) B :=
    fun B => contains_of_empty_rows 1 le_rfl B
  have hne : ¬ ∃ B : BMat 1 1, Free (fun (_ : Fin 0) (_ : Fin 1) => false) B := by
    rintro ⟨B, hB⟩
    exact hB (hContains B)
  have hS : {d : ℕ | ∃ B : BMat 1 1,
      Free (fun (_ : Fin 0) (_ : Fin 1) => false) B ∧ hamming (zeros 1 1) B = d} = ∅ := by
    ext d
    constructor
    · rintro ⟨B, hB, -⟩
      exact hne ⟨B, hB⟩
    · intro hd
      exact absurd hd (by simp)
  have hzero : editDist (fun (_ : Fin 0) (_ : Fin 1) => false) (zeros 1 1) = 0 := by
    rw [editDist, hS, Nat.sInf_empty]
  intro h
  exact (h.mp hzero) (hContains (zeros 1 1))

/-- There is no proof of the frozen §2 statement as universally stated. -/
theorem no_section2_editDist_eq_zero_iff :
    ¬ (∀ {k l n m : ℕ} (H : BMat k l) (A : BMat n m), editDist H A = 0 ↔ Free H A) := by
  intro h
  exact editDist_eq_zero_iff_counterexample
    (h (fun (_ : Fin 0) (_ : Fin 1) => false) (zeros 1 1))

end OrderedRemoval

#print axioms OrderedRemoval.no_section2_editDist_eq_zero_iff
