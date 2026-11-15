/-
Direct sums of ordered-removal counterexamples: definitions and statements.

Paper notation → Lean:
  k × l binary pattern H                `H : BMat k l`   (`true` = 1, `false` = 0)
  n × n host A                          `A : BMat n n`
  ordered copy (r₁<…<r_k, c₁<…<c_l)     `IsCopy H A r c`  (strictly monotone `r`, `c`)
  N_H(A)                                `copyCount H A`   (counts pairs of index maps)
  D_H(A)                                `editDist H A`
  [H 0; 0 Z]                            `blockDiag H Z`
  Ẑ (each entry of Z a qn × pn block)   `blowup Z n`      (size p·q·n on both axes)
  A⁺ = [A 0; 0 Ẑ]                       `blockDiag A (blowup Z n)`
  "rows of Z pairwise distinct"         `Function.Injective Z`
  "columns of Z pairwise distinct"      `Function.Injective (fun j i => Z i j)`

Indices are 0-based.  Every theorem below is a statement only (`sorry`).
Order of work: §2 sanity lemmas, then §3 (Z = (1)) and §4 (zero columns),
then §5 (general Z), then §6 (the corollary).
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OrderedRemoval

open Classical

/-! ## 1. Definitions -/

/-- A binary matrix with `a` rows and `b` columns; `true` stands for 1. -/
abbrev BMat (a b : ℕ) := Fin a → Fin b → Bool

/-- The rows `r` and columns `c` (both strictly increasing) carry an ordered copy of `H` in `A`:
every entry of `H`, 0 or 1, is matched. -/
def IsCopy {k l n m : ℕ} (H : BMat k l) (A : BMat n m) (r : Fin k → Fin n) (c : Fin l → Fin m) :
    Prop :=
  StrictMono r ∧ StrictMono c ∧ ∀ i j, A (r i) (c j) = H i j

/-- `A` contains `H` as an ordered copy. -/
def Contains {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ∃ r c, IsCopy H A r c

/-- `A` is `H`-free. -/
def Free {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ¬ Contains H A

/-- `N_H(A)`: the number of ordered copies, i.e. of pairs of strictly increasing index maps. -/
noncomputable def copyCount {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=
  (Finset.univ.filter
    (fun rc : (Fin k → Fin n) × (Fin l → Fin m) => IsCopy H A rc.1 rc.2)).card

/-- The number of entries in which `A` and `B` differ. -/
noncomputable def hamming {n m : ℕ} (A B : BMat n m) : ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2)).card

/-- `D_H(A)`: the least number of entries to change to make `A` `H`-free.
(If no `H`-free matrix of this shape exists, `sInf ∅ = 0`; this never happens when `H` has a 1,
see `free_zero`.) -/
noncomputable def editDist {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=
  sInf {d | ∃ B : BMat n m, Free H B ∧ hamming A B = d}

/-- Polynomial removal for an `a × b` pattern `H`, on square hosts:
there are `c, C > 0` such that every `n × n` matrix `A` with `D_H(A) ≥ ε n²` (`0 < ε ≤ 1`)
has `N_H(A) ≥ c ε^C n^(a+b)`.  `ε ^ C` is the real power. -/
def PolyRemoval {a b : ℕ} (H : BMat a b) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (n : ℕ) (A : BMat n n) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ε * (n : ℝ) ^ 2 ≤ (editDist H A : ℝ) →
        c * ε ^ C * (n : ℝ) ^ (a + b) ≤ (copyCount H A : ℝ)

/-- The block-diagonal matrix `[H 0; 0 Z]`, rows and columns of `H` first. -/
def blockDiag {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) : BMat (k + p) (l + q) :=
  fun i j =>
    Fin.addCases (motive := fun _ => Bool)
      (fun i' => Fin.addCases (motive := fun _ => Bool) (fun j' => H i' j') (fun _ => false) j)
      (fun i' => Fin.addCases (motive := fun _ => Bool) (fun _ => false) (fun j' => Z i' j') j) i

/-- The all-ones `n × n` matrix. -/
def ones (a b : ℕ) : BMat a b := fun _ _ => true

/-- The all-zeros `a × b` matrix. -/
def zeros (a b : ℕ) : BMat a b := fun _ _ => false

/-- `H` with `q` all-zero columns appended on the right. -/
def appendZeroCols {k l : ℕ} (H : BMat k l) (q : ℕ) : BMat k (l + q) :=
  fun i j => Fin.addCases (motive := fun _ => Bool) (fun j' => H i j') (fun _ => false) j

/-- `Ẑ`: every entry of the `p × q` matrix `Z` replaced by a constant block with `q·n` rows and
`p·n` columns.  Row `i` lies in group `i / (q n)`, column `j` in group `j / (p n)`. -/
def blowup {p q : ℕ} (Z : BMat p q) (n : ℕ) : BMat (p * q * n) (p * q * n) :=
  fun i j =>
    Z ⟨i.val / (q * n), Nat.div_lt_of_lt_mul (by
        have h := i.isLt
        simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩
      ⟨j.val / (p * n), Nat.div_lt_of_lt_mul (by
        have h := j.isLt
        simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩

/-- No all-zero row and no all-zero column. -/
def NoZeroLine {k l : ℕ} (H : BMat k l) : Prop :=
  (∀ i, ∃ j, H i j = true) ∧ (∀ j, ∃ i, H i j = true)

/-! ## 2. Sanity lemmas about the definitions (prove these first) -/

/-- `hamming A B = 0` iff `A = B`. -/
theorem hamming_eq_zero_iff {n m : ℕ} (A B : BMat n m) : hamming A B = 0 ↔ A = B := by
  simp only [hamming, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_true_left, not_not, Prod.forall]
  constructor
  · intro h
    funext i j
    exact h i j
  · rintro rfl i j
    rfl

/-- `hamming A A = 0`. -/
theorem hamming_self {n m : ℕ} (A : BMat n m) : hamming A A = 0 := by
  rw [hamming_eq_zero_iff]

/-- A pattern with a 1 is absent from the zero matrix. -/
theorem free_zero {k l n m : ℕ} (H : BMat k l) (h : ∃ i j, H i j = true) :
    Free H (zeros n m) := by
  obtain ⟨i, j, hij⟩ := h
  rintro ⟨r, c, -, -, hrc⟩
  have h1 := hrc i j
  simp only [zeros] at h1
  rw [← h1] at hij
  simp at hij

/-- `editDist` is attained by an `H`-free matrix, when one exists. -/
theorem editDist_spec {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (h : ∃ B : BMat n m, Free H B) :
    ∃ B : BMat n m, Free H B ∧ hamming A B = editDist H A := by
  have hne : ({d | ∃ B : BMat n m, Free H B ∧ hamming A B = d} : Set ℕ).Nonempty := by
    obtain ⟨B, hB⟩ := h
    exact ⟨hamming A B, B, hB, rfl⟩
  exact Nat.sInf_mem hne

/-- `editDist` is at most the distance to any `H`-free matrix. -/
theorem editDist_le {k l n m : ℕ} (H : BMat k l) (A B : BMat n m) (hB : Free H B) :
    editDist H A ≤ hamming A B := by
  exact Nat.sInf_le ⟨B, hB, rfl⟩

/-- `editDist H A = 0` exactly when `A` is `H`-free. -/
theorem editDist_eq_zero_iff {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (hfree : ∃ B : BMat n m, Free H B) :
    editDist H A = 0 ↔ Free H A := by
  constructor
  · intro h0
    obtain ⟨B, hB, hAB⟩ := editDist_spec H A hfree
    rw [h0, hamming_eq_zero_iff] at hAB
    rwa [hAB]
  · intro hA
    have hle : editDist H A ≤ hamming A A := editDist_le H A A hA
    rw [hamming_self] at hle
    exact Nat.le_zero.mp hle

/-- `hamming` is symmetric. -/
theorem hamming_comm {n m : ℕ} (A B : BMat n m) : hamming A B = hamming B A := by
  simp only [hamming, ne_comm]

/-- The Hamming distance is bounded by the total number of entries. -/
theorem hamming_le_card {n m : ℕ} (A B : BMat n m) : hamming A B ≤ n * m := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n × Fin m))
    (fun x => A x.1 x.2 ≠ B x.1 x.2)
  simpa [hamming, Fintype.card_prod, Fintype.card_fin] using h

/-- If `H` has a `1` there is an `H`-free matrix of any shape, so `editDist` is at most
the number of entries.  This is the estimate `D ≤ n^2` used in Step 3 of the paper. -/
theorem editDist_le_card {k l n m : ℕ} (H : BMat k l) (A : BMat n m)
    (h : ∃ i j, H i j = true) : editDist H A ≤ n * m :=
  (editDist_le H A (zeros n m) (free_zero H h)).trans (hamming_le_card A (zeros n m))

/-- `copyCount H A = 0` exactly when `A` is `H`-free. -/
theorem copyCount_eq_zero_iff {k l n m : ℕ} (H : BMat k l) (A : BMat n m) :
    copyCount H A = 0 ↔ Free H A := by
  simp only [copyCount, Free, Contains, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, forall_true_left, not_exists, Prod.forall]

/-! ### When does `hfree` hold?

`editDist_spec` and `editDist_eq_zero_iff` need a witness matrix that is `H`-free, since
`sInf ∅ = 0` in `ℕ` would otherwise make `editDist` collapse to `0`.  The next lemmas record
that (a) `hfree` is provable as soon as `0 < k` and `0 < l`, and (b) `hfree` is *not* redundant.
-/

/-- If `H` has a `1`, `ones` contains `H` unless `H` is all-zero; concretely, an all-zero `H`
never matches an all-ones matrix. -/
theorem free_ones {k l n m : ℕ} (H : BMat k l) (hk : 0 < k) (hl : 0 < l)
    (h : ∀ i j, H i j = false) : Free H (ones n m) := by
  rintro ⟨r, c, -, -, hrc⟩
  have h1 := hrc ⟨0, hk⟩ ⟨0, hl⟩
  simp only [ones] at h1
  rw [h ⟨0, hk⟩ ⟨0, hl⟩] at h1
  simp at h1

/-- A pattern with at least one row and one column has a free matrix of every shape: the zero
matrix if `H` has a `1`, the all-ones matrix otherwise. -/
theorem exists_free {k l : ℕ} (H : BMat k l) (hk : 0 < k) (hl : 0 < l) (n m : ℕ) :
    ∃ B : BMat n m, Free H B := by
  by_cases h : ∃ i j, H i j = true
  · exact ⟨zeros n m, free_zero H h⟩
  · refine ⟨ones n m, free_ones H hk hl ?_⟩
    intro i j
    cases eq : H i j with
    | false => rfl
    | true => exact absurd ⟨i, j, eq⟩ h

/-- `NoZeroLine H` and `0 < k` force `0 < l`, so `hH` and `hk` supply the hypotheses of
`exists_free` for `H`. -/
theorem lt_of_noZeroLine {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k) :
    0 < l := by
  obtain ⟨j, -⟩ := hH.1 ⟨0, hk⟩
  exact j.pos

namespace DirectSumAux

open Classical

/-! ## A. `Fin` index toolkit

`Fin.castAdd`/`Fin.natAdd` are how `blockDiag` splits rows and columns into an "old" and a
"new" part; these are the small order/equality facts about them that every later step needs. -/

theorem fin_castAdd_val {m n : ℕ} (i : Fin m) : (Fin.castAdd n i).val = i.val := Fin.val_castAdd n i

theorem fin_natAdd_val {m n : ℕ} (i : Fin n) : (Fin.natAdd m i).val = m + i.val := Fin.val_natAdd m i

theorem castAdd_lt_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) : Fin.castAdd n i < Fin.natAdd m j := by
  rw [Fin.lt_def, fin_castAdd_val, fin_natAdd_val]; omega

theorem castAdd_lt_castAdd_iff {m n : ℕ} {i j : Fin m} :
    Fin.castAdd n i < Fin.castAdd n j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def, fin_castAdd_val, fin_castAdd_val]

theorem castAdd_le_castAdd_iff {m n : ℕ} {i j : Fin m} :
    Fin.castAdd n i ≤ Fin.castAdd n j ↔ i ≤ j := by
  rw [Fin.le_def, Fin.le_def, fin_castAdd_val, fin_castAdd_val]

theorem castAdd_eq_castAdd_iff {m n : ℕ} {i j : Fin m} :
    Fin.castAdd n i = Fin.castAdd n j ↔ i = j := Fin.castAdd_inj

theorem natAdd_eq_natAdd_iff {m n : ℕ} {i j : Fin n} :
    Fin.natAdd m i = Fin.natAdd m j ↔ i = j := Fin.natAdd_inj m

theorem natAdd_lt_natAdd_iff {m n : ℕ} {i j : Fin n} :
    Fin.natAdd m i < Fin.natAdd m j ↔ i < j := Fin.natAdd_lt_natAdd_iff m

theorem natAdd_le_natAdd_iff {m n : ℕ} {i j : Fin n} :
    Fin.natAdd m i ≤ Fin.natAdd m j ↔ i ≤ j := Fin.natAdd_le_natAdd_iff m

/-- Every index of `Fin (m + n)` is either a cast of an index of `Fin m` or a shift of an
index of `Fin n`. -/
theorem eq_castAdd_or_natAdd {m n : ℕ} (i : Fin (m + n)) :
    (∃ i' : Fin m, i = Fin.castAdd n i') ∨ (∃ i' : Fin n, i = Fin.natAdd m i') := by
  rcases Nat.lt_or_ge i.val m with h | h
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext (by rw [fin_castAdd_val])⟩
  · have hlt : i.val - m < n := by have := i.isLt; omega
    exact Or.inr ⟨⟨i.val - m, hlt⟩, Fin.ext (by show i.val = m + (i.val - m); omega)⟩

/-- An index in the "old" range is below every index in the "new" range. -/
theorem old_lt_new {m n : ℕ} {i : Fin (m + n)} (hi : i.val < m) {j : Fin (m + n)} (hj : m ≤ j.val) :
    i < j := by
  rw [Fin.lt_def]; omega

/-- Gluing two strictly increasing index maps, the first entirely below the second, gives a
strictly increasing index map on `Fin (m + n)`.  This is how a copy of `[H 0; 0 Z]` is
assembled from a copy of `H` plus the extra rows and columns. -/
theorem strictMono_append {m n N : ℕ} {f : Fin m → Fin N} {g : Fin n → Fin N}
    (hf : StrictMono f) (hg : StrictMono g) (h : ∀ i j, f i < g j) :
    StrictMono (Fin.append f g) := by
  intro a b hab
  obtain ⟨a', rfl⟩ | ⟨a', rfl⟩ := eq_castAdd_or_natAdd a
  · obtain ⟨b', rfl⟩ | ⟨b', rfl⟩ := eq_castAdd_or_natAdd b
    · rw [Fin.append_left, Fin.append_left]
      exact hf (by rwa [castAdd_lt_castAdd_iff] at hab)
    · rw [Fin.append_left, Fin.append_right]
      exact h a' b'
  · obtain ⟨b', rfl⟩ | ⟨b', rfl⟩ := eq_castAdd_or_natAdd b
    · exact absurd hab (not_lt_of_ge (le_of_lt (castAdd_lt_natAdd b' a')))
    · rw [Fin.append_right, Fin.append_right]
      exact hg (by rwa [natAdd_lt_natAdd_iff] at hab)

/-- `Fin.append` of two strictly increasing maps is strictly increasing on each part. -/
theorem strictMono_append_left {m n N : ℕ} {f : Fin m → Fin N} {g : Fin n → Fin N}
    (h : StrictMono (Fin.append f g)) : StrictMono f := by
  intro i j hij
  have := h (show Fin.castAdd n i < Fin.castAdd n j by rwa [castAdd_lt_castAdd_iff])
  rwa [Fin.append_left, Fin.append_left] at this

theorem strictMono_append_right {m n N : ℕ} {f : Fin m → Fin N} {g : Fin n → Fin N}
    (h : StrictMono (Fin.append f g)) : StrictMono g := by
  intro i j hij
  have := h (show Fin.natAdd m i < Fin.natAdd m j by rwa [natAdd_lt_natAdd_iff])
  rwa [Fin.append_right, Fin.append_right] at this

theorem append_left_lt_right {m n N : ℕ} {f : Fin m → Fin N} {g : Fin n → Fin N}
    (h : StrictMono (Fin.append f g)) (i : Fin m) (j : Fin n) : f i < g j := by
  have := h (castAdd_lt_natAdd i j)
  rwa [Fin.append_left, Fin.append_right] at this




open Classical

/-! ## B. Entries of `blockDiag`

`blockDiag H Z` is `[H 0; 0 Z]`.  Two layers of `Fin.addCases`; these lemmas say what each
of the four blocks contains. -/

theorem blockDiag_castAdd_castAdd {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin k) (j : Fin l) :
    blockDiag H Z (Fin.castAdd p i) (Fin.castAdd q j) = H i j := by
  simp only [blockDiag, Fin.addCases_left]

theorem blockDiag_castAdd_natAdd {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin k) (j : Fin q) :
    blockDiag H Z (Fin.castAdd p i) (Fin.natAdd l j) = false := by
  simp only [blockDiag, Fin.addCases_left, Fin.addCases_right]

theorem blockDiag_natAdd_castAdd {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin p) (j : Fin l) :
    blockDiag H Z (Fin.natAdd k i) (Fin.castAdd q j) = false := by
  simp only [blockDiag, Fin.addCases_right, Fin.addCases_left]

theorem blockDiag_natAdd_natAdd {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin p) (j : Fin q) :
    blockDiag H Z (Fin.natAdd k i) (Fin.natAdd l j) = Z i j := by
  simp only [blockDiag, Fin.addCases_right]

/-! Coordinate-free forms: whether an index falls in the old or the new range decides the
block.  These are what `Step 1` uses, since a copy's rows arrive as bare `Fin (k + p)`. -/

theorem castAdd_of_val_lt {m n : ℕ} {i : Fin (m + n)} (h : i.val < m) :
    i = Fin.castAdd n ⟨i.val, h⟩ := Fin.ext (by rw [fin_castAdd_val])

theorem natAdd_of_val_ge {m n : ℕ} {i : Fin (m + n)} (h : m ≤ i.val) :
    i = Fin.natAdd m ⟨i.val - m, by have := i.isLt; omega⟩ :=
  Fin.ext (by show i.val = m + (i.val - m); omega)

theorem blockDiag_apply_old_old {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    {i : Fin (k + p)} {j : Fin (l + q)} (hi : i.val < k) (hj : j.val < l) :
    blockDiag H Z i j = H ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  obtain ⟨i', rfl⟩ : ∃ i' : Fin k, i = Fin.castAdd p i' := ⟨⟨i.val, hi⟩, castAdd_of_val_lt hi⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin l, j = Fin.castAdd q j' := ⟨⟨j.val, hj⟩, castAdd_of_val_lt hj⟩
  exact blockDiag_castAdd_castAdd H Z i' j'

theorem blockDiag_apply_old_new {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    {i : Fin (k + p)} {j : Fin (l + q)} (hi : i.val < k) (hj : l ≤ j.val) :
    blockDiag H Z i j = false := by
  obtain ⟨i', rfl⟩ : ∃ i' : Fin k, i = Fin.castAdd p i' := ⟨⟨i.val, hi⟩, castAdd_of_val_lt hi⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin q, j = Fin.natAdd l j' :=
    ⟨⟨j.val - l, by have := j.isLt; omega⟩, natAdd_of_val_ge hj⟩
  exact blockDiag_castAdd_natAdd H Z i' j'

theorem blockDiag_apply_new_old {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    {i : Fin (k + p)} {j : Fin (l + q)} (hi : k ≤ i.val) (hj : j.val < l) :
    blockDiag H Z i j = false := by
  obtain ⟨i', rfl⟩ : ∃ i' : Fin p, i = Fin.natAdd k i' :=
    ⟨⟨i.val - k, by have := i.isLt; omega⟩, natAdd_of_val_ge hi⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin l, j = Fin.castAdd q j' := ⟨⟨j.val, hj⟩, castAdd_of_val_lt hj⟩
  exact blockDiag_natAdd_castAdd H Z i' j'

theorem blockDiag_apply_new_new {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    {i : Fin (k + p)} {j : Fin (l + q)} (hi : k ≤ i.val) (hj : l ≤ j.val) :
    blockDiag H Z i j
      = Z ⟨i.val - k, by have := i.isLt; omega⟩ ⟨j.val - l, by have := j.isLt; omega⟩ := by
  obtain ⟨i', rfl⟩ : ∃ i' : Fin p, i = Fin.natAdd k i' :=
    ⟨⟨i.val - k, by have := i.isLt; omega⟩, natAdd_of_val_ge hi⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin q, j = Fin.natAdd l j' :=
    ⟨⟨j.val - l, by have := j.isLt; omega⟩, natAdd_of_val_ge hj⟩
  rw [blockDiag_natAdd_natAdd]
  simp

/-- In `[H 0; 0 Z]`, an entry with an old row and a new column is `0`. -/
theorem blockDiag_old_new_false {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin k) (j : Fin q) : blockDiag H Z (Fin.castAdd p i) (Fin.natAdd l j) = false :=
  blockDiag_castAdd_natAdd H Z i j

/-- Consequently an old row of `[X 0; 0 Z]` has no `1` in a new column. -/
theorem blockDiag_old_row_new_col_ne_true {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin k) (j : Fin q) : blockDiag H Z (Fin.castAdd p i) (Fin.natAdd l j) ≠ true := by
  rw [blockDiag_castAdd_natAdd]; exact Bool.false_ne_true

theorem blockDiag_new_row_old_col_ne_true {k l p q : ℕ} (H : BMat k l) (Z : BMat p q)
    (i : Fin p) (j : Fin l) : blockDiag H Z (Fin.natAdd k i) (Fin.castAdd q j) ≠ true := by
  rw [blockDiag_natAdd_castAdd]; exact Bool.false_ne_true




open Classical

/-! ## C. The blow-up `Ẑ`

`blowup Z n` is the `(p*q*n) × (p*q*n)` matrix in which entry `Z i j` is replaced by the
constant block of size `(q*n) × (p*n)`.  Rows therefore come in `p` groups of `q*n` identical
rows (indexed by `i.val / (q*n)`, a row of `Z`), columns in `q` groups of `p*n` identical
columns (indexed by `j.val / (p*n)`, a column of `Z`). -/

section Entries

variable {p q n : ℕ}

/-- Entry formula for `blowup`, exactly as the definition produces it. -/
theorem blowup_apply (Z : BMat p q) (i j : Fin (p * q * n)) :
    blowup Z n i j =
      Z ⟨i.val / (q * n), Nat.div_lt_of_lt_mul (by
            have h := i.isLt
            simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩
        ⟨j.val / (p * n), Nat.div_lt_of_lt_mul (by
            have h := j.isLt
            simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩ := rfl

/-- Entry formula for `blowup`, with the bounds supplied by the caller. -/
theorem blowup_apply' (Z : BMat p q) (i j : Fin (p * q * n))
    (hi : i.val / (q * n) < p) (hj : j.val / (p * n) < q) :
    blowup Z n i j = Z ⟨i.val / (q * n), hi⟩ ⟨j.val / (p * n), hj⟩ := by
  rw [blowup_apply]

/-- The row group of `i` is a row of `Z`. -/
theorem blowup_row_lt (i : Fin (p * q * n)) : i.val / (q * n) < p := by
  refine Nat.div_lt_of_lt_mul ?_
  calc i.val < p * q * n := i.isLt
    _ = q * n * p := by ring

/-- The column group of `j` is a column of `Z`. -/
theorem blowup_col_lt (j : Fin (p * q * n)) : j.val / (p * n) < q := by
  refine Nat.div_lt_of_lt_mul ?_
  calc j.val < p * q * n := j.isLt
    _ = p * n * q := by ring

/-- Two indices with the same row group give the same row of `blowup Z n`. -/
theorem blowup_row_congr (Z : BMat p q) {i i' : Fin (p * q * n)}
    (h : i.val / (q * n) = i'.val / (q * n)) (j : Fin (p * q * n)) :
    blowup Z n i j = blowup Z n i' j := by
  rw [blowup_apply, blowup_apply]
  exact congrArg₂ Z (Fin.ext h) (Fin.ext rfl)

/-- Two indices with the same column group give the same column of `blowup Z n`. -/
theorem blowup_col_congr (Z : BMat p q) {j j' : Fin (p * q * n)}
    (h : j.val / (p * n) = j'.val / (p * n)) (i : Fin (p * q * n)) :
    blowup Z n i j = blowup Z n i j' := by
  rw [blowup_apply, blowup_apply]
  exact congrArg₂ Z (Fin.ext rfl) (Fin.ext h)

/-- Rows of `blowup Z n` in the same group are equal as functions. -/
theorem blowup_row_eq (Z : BMat p q) {i i' : Fin (p * q * n)}
    (h : i.val / (q * n) = i'.val / (q * n)) : blowup Z n i = blowup Z n i' :=
  funext (blowup_row_congr Z h)

/-- Columns of `blowup Z n` in the same group are equal as functions. -/
theorem blowup_col_eq (Z : BMat p q) {j j' : Fin (p * q * n)}
    (h : j.val / (p * n) = j'.val / (p * n)) : (fun i => blowup Z n i j) = fun i => blowup Z n i j' :=
  funext (blowup_col_congr Z h)

end Entries

/-! ### The groups, concretely -/

section Groups

variable {p q n : ℕ}

/-- The canonical index in row group `a` at offset `t`, for `a : Fin p` and `t : Fin (q*n)`. -/
def rowRep (a : Fin p) (t : Fin (q * n)) : Fin (p * q * n) :=
  ⟨a.val * (q * n) + t.val, by
    have ht : t.val < q * n := t.isLt
    have ha : a.val < p := a.isLt
    calc a.val * (q * n) + t.val < a.val * (q * n) + q * n := by omega
      _ = (a.val + 1) * (q * n) := by ring
      _ ≤ p * (q * n) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
      _ = p * q * n := by ring⟩

/-- The canonical index in column group `b` at offset `t`, for `b : Fin q` and `t : Fin (p*n)`. -/
def colRep (b : Fin q) (t : Fin (p * n)) : Fin (p * q * n) :=
  ⟨b.val * (p * n) + t.val, by
    have ht : t.val < p * n := t.isLt
    have hb : b.val < q := b.isLt
    calc b.val * (p * n) + t.val < b.val * (p * n) + p * n := by omega
      _ = (b.val + 1) * (p * n) := by ring
      _ ≤ q * (p * n) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)
      _ = p * q * n := by ring⟩

theorem rowRep_val (a : Fin p) (t : Fin (q * n)) :
    (rowRep a t).val = a.val * (q * n) + t.val := rfl

theorem colRep_val (b : Fin q) (t : Fin (p * n)) :
    (colRep b t).val = b.val * (p * n) + t.val := rfl

theorem rowRep_group (hn : 0 < q * n) (a : Fin p) (t : Fin (q * n)) :
    (rowRep a t).val / (q * n) = a.val := by
  rw [rowRep_val]
  have h1 : a.val * (q * n) + t.val = t.val + (q * n) * a.val := by
    rw [Nat.mul_comm a.val (q * n), Nat.add_comm]
  rw [h1, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt t.isLt, Nat.zero_add]

theorem colRep_group (hn : 0 < p * n) (b : Fin q) (t : Fin (p * n)) :
    (colRep b t).val / (p * n) = b.val := by
  rw [colRep_val]
  have h1 : b.val * (p * n) + t.val = t.val + (p * n) * b.val := by
    rw [Nat.mul_comm b.val (p * n), Nat.add_comm]
  rw [h1, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt t.isLt, Nat.zero_add]

theorem rowRep_injective (q : ℕ) (a : Fin p) :
    Function.Injective (rowRep (q := q) (n := n) a) := by
  intro t t' h
  have h' := congrArg Fin.val h
  simp only [rowRep_val] at h'
  exact Fin.ext (Nat.add_left_cancel h')

theorem colRep_injective (p : ℕ) (b : Fin q) :
    Function.Injective (colRep (p := p) (n := n) b) := by
  intro t t' h
  have h' := congrArg Fin.val h
  simp only [colRep_val] at h'
  exact Fin.ext (Nat.add_left_cancel h')

theorem rowRep_surjective (hn : 0 < q * n) (a : Fin p) {i : Fin (p * q * n)}
    (hi : i.val / (q * n) = a.val) : ∃ t : Fin (q * n), rowRep a t = i := by
  refine ⟨⟨i.val % (q * n), Nat.mod_lt _ hn⟩, ?_⟩
  apply Fin.ext
  rw [rowRep_val]
  show a.val * (q * n) + i.val % (q * n) = i.val
  rw [← hi, Nat.mul_comm (i.val / (q * n)) (q * n), Nat.div_add_mod]

theorem colRep_surjective (hn : 0 < p * n) (b : Fin q) {i : Fin (p * q * n)}
    (hi : i.val / (p * n) = b.val) : ∃ t : Fin (p * n), colRep b t = i := by
  refine ⟨⟨i.val % (p * n), Nat.mod_lt _ hn⟩, ?_⟩
  apply Fin.ext
  rw [colRep_val]
  show b.val * (p * n) + i.val % (p * n) = i.val
  rw [← hi, Nat.mul_comm (i.val / (p * n)) (p * n), Nat.div_add_mod]

/-- The number of indices in a given row group of `blowup Z n` is `q * n`. -/
theorem blowup_row_group_card (hn : 0 < q * n) (a : Fin p) :
    (Finset.univ.filter (fun i : Fin (p * q * n) => i.val / (q * n) = a.val)).card = q * n := by
  have himg : Finset.univ.filter (fun i : Fin (p * q * n) => i.val / (q * n) = a.val)
      = Finset.univ.image (rowRep (n := n) a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun h => rowRep_surjective hn a h, fun ⟨t, ht⟩ => by rw [← ht, rowRep_group hn]⟩
  rw [himg, Finset.card_image_of_injective _ (rowRep_injective q a), Finset.card_univ,
    Fintype.card_fin]

/-- The number of indices in a given column group of `blowup Z n` is `p * n`. -/
theorem blowup_col_card (hn : 0 < p * n) (b : Fin q) :
    (Finset.univ.filter (fun j : Fin (p * q * n) => j.val / (p * n) = b.val)).card = p * n := by
  have himg : Finset.univ.filter (fun j : Fin (p * q * n) => j.val / (p * n) = b.val)
      = Finset.univ.image (colRep (n := n) b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun h => colRep_surjective hn b h, fun ⟨t, ht⟩ => by rw [← ht, colRep_group hn]⟩
  rw [himg, Finset.card_image_of_injective _ (colRep_injective p b), Finset.card_univ,
    Fintype.card_fin]

end Groups

/-! ### Interaction with `blockDiag` and the special patterns -/

section BlockDiagBlowup

variable {k l p q n : ℕ}

theorem blockDiag_blowup_natAdd_natAdd (A : BMat n n) (Z : BMat p q)
    (i j : Fin (p * q * n)) :
    blockDiag A (blowup Z n) (Fin.natAdd n i) (Fin.natAdd n j) = blowup Z n i j :=
  blockDiag_natAdd_natAdd A (blowup Z n) i j

theorem blockDiag_blowup_natAdd_castAdd (A : BMat n n) (Z : BMat p q)
    (i : Fin (p * q * n)) (j : Fin n) :
    blockDiag A (blowup Z n) (Fin.natAdd n i) (Fin.castAdd (p * q * n) j) = false :=
  blockDiag_natAdd_castAdd A (blowup Z n) i j

theorem blockDiag_blowup_castAdd_natAdd (A : BMat n n) (Z : BMat p q)
    (i : Fin n) (j : Fin (p * q * n)) :
    blockDiag A (blowup Z n) (Fin.castAdd (p * q * n) i) (Fin.natAdd n j) = false :=
  blockDiag_castAdd_natAdd A (blowup Z n) i j

/-- New rows of `blockDiag A (blowup Z n)` in the same group are equal. -/
theorem blockDiag_blowup_row_congr (A : BMat n n) (Z : BMat p q) {i i' : Fin (p * q * n)}
    (h : i.val / (q * n) = i'.val / (q * n)) (j : Fin (n + p * q * n)) :
    blockDiag A (blowup Z n) (Fin.natAdd n i) j
      = blockDiag A (blowup Z n) (Fin.natAdd n i') j := by
  obtain ⟨j', rfl⟩ | ⟨j', rfl⟩ := eq_castAdd_or_natAdd j
  · rw [blockDiag_blowup_natAdd_castAdd, blockDiag_blowup_natAdd_castAdd]
  · rw [blockDiag_blowup_natAdd_natAdd, blockDiag_blowup_natAdd_natAdd, blowup_row_congr Z h]

/-- New columns of `blockDiag A (blowup Z n)` in the same group are equal. -/
theorem blockDiag_blowup_col_congr (A : BMat n n) (Z : BMat p q) {j j' : Fin (p * q * n)}
    (h : j.val / (p * n) = j'.val / (p * n)) (i : Fin (n + p * q * n)) :
    blockDiag A (blowup Z n) i (Fin.natAdd n j)
      = blockDiag A (blowup Z n) i (Fin.natAdd n j') := by
  obtain ⟨i', rfl⟩ | ⟨i', rfl⟩ := eq_castAdd_or_natAdd i
  · rw [blockDiag_blowup_castAdd_natAdd, blockDiag_castAdd_natAdd]
  · rw [blockDiag_blowup_natAdd_natAdd, blockDiag_blowup_natAdd_natAdd, blowup_col_congr Z h]

end BlockDiagBlowup

section Special

theorem ones_apply {a b : ℕ} (i : Fin a) (j : Fin b) : ones a b i j = true := rfl

theorem zeros_apply {a b : ℕ} (i : Fin a) (j : Fin b) : zeros a b i j = false := rfl

theorem blowup_ones_apply (p q n : ℕ) (i j : Fin (p * q * n)) :
    blowup (ones p q) n i j = true := rfl

theorem blowup_zeros_apply (p q n : ℕ) (i j : Fin (p * q * n)) :
    blowup (zeros p q) n i j = false := rfl

/-- Blowing up an all-ones pattern gives an all-ones matrix (same shape). -/
theorem blowup_ones_eq (p q n : ℕ) :
    blowup (ones p q) n = ones (p * q * n) (p * q * n) :=
  funext fun i => funext (blowup_ones_apply p q n i)

theorem blowup_zeros_eq (p q n : ℕ) :
    blowup (zeros p q) n = zeros (p * q * n) (p * q * n) :=
  funext fun i => funext (blowup_zeros_apply p q n i)

end Special

section AppendZeroCols

variable {k l : ℕ}

theorem appendZeroCols_castAdd (H : BMat k l) (q : ℕ) (i : Fin k) (j : Fin l) :
    appendZeroCols H q i (Fin.castAdd q j) = H i j := by
  simp only [appendZeroCols, Fin.addCases_left]

theorem appendZeroCols_natAdd (H : BMat k l) (q : ℕ) (i : Fin k) (j : Fin q) :
    appendZeroCols H q i (Fin.natAdd l j) = false := by
  simp only [appendZeroCols, Fin.addCases_right]

theorem appendZeroCols_apply_old {H : BMat k l} {q : ℕ} {i : Fin k} {j : Fin (l + q)}
    (hj : j.val < l) : appendZeroCols H q i j = H i ⟨j.val, hj⟩ := by
  obtain ⟨j', rfl⟩ : ∃ j' : Fin l, j = Fin.castAdd q j' := ⟨⟨j.val, hj⟩, castAdd_of_val_lt hj⟩
  exact appendZeroCols_castAdd H q i j'

end AppendZeroCols




open Classical

/-! ## D. `hamming` and `copyCount` as finite sums

`hamming` and `copyCount` are defined by `Finset.card` of a `filter`.  Every counting argument
in the paper (Step 2's injection and Step 3's double count) works with the indicator sums
instead, so these two bridges are needed everywhere. -/

section Hamming

variable {n m : ℕ}

theorem hamming_eq_sum (A B : BMat n m) :
    hamming A B = ∑ x : Fin n × Fin m, (if A x.1 x.2 = B x.1 x.2 then 0 else 1) := by
  rw [hamming, Finset.card_filter]
  simp

theorem hamming_eq_sum' (A B : BMat n m) :
    hamming A B = ∑ i : Fin n, ∑ j : Fin m, (if A i j = B i j then 0 else 1) := by
  rw [hamming_eq_sum, Fintype.sum_prod_type]

theorem hamming_comm (A B : BMat n m) : hamming A B = hamming B A := by
  simp only [hamming_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : A x.1 x.2 = B x.1 x.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hamming_self (A : BMat n m) : hamming A A = 0 := by
  simp [hamming_eq_sum]

theorem hamming_eq_zero_iff (A B : BMat n m) : hamming A B = 0 ↔ A = B := by
  rw [hamming, Finset.card_eq_zero]
  constructor
  · intro h
    funext i j
    by_contra hne
    have hmem : (i, j) ∈ Finset.univ.filter (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2) := by
      simp [hne]
    rw [h] at hmem
    simp at hmem
  · rintro rfl
    simp

theorem hamming_le (A B : BMat n m) : hamming A B ≤ n * m := by
  rw [hamming_eq_sum]
  calc ∑ x : Fin n × Fin m, (if A x.1 x.2 = B x.1 x.2 then 0 else 1)
      ≤ ∑ _x : Fin n × Fin m, 1 := by
        refine Finset.sum_le_sum fun x _ => ?_
        split <;> omega
    _ = n * m := by simp [Fintype.card_prod]

end Hamming

section CopyCount

variable {k l n m : ℕ}

theorem copyCount_eq_sum (H : BMat k l) (A : BMat n m) :
    copyCount H A = ∑ rc : (Fin k → Fin n) × (Fin l → Fin m),
      (if IsCopy H A rc.1 rc.2 then 1 else 0) := by
  rw [copyCount, Finset.card_filter]

theorem copyCount_eq_sum' (H : BMat k l) (A : BMat n m) :
    copyCount H A = ∑ r : Fin k → Fin n, ∑ c : Fin l → Fin m,
      (if IsCopy H A r c then 1 else 0) := by
  rw [copyCount_eq_sum, Fintype.sum_prod_type]

/-- Crude bound: at most `n^k * m^l` copies. -/
theorem copyCount_le (H : BMat k l) (A : BMat n m) : copyCount H A ≤ n ^ k * m ^ l := by
  rw [copyCount_eq_sum']
  calc ∑ r : Fin k → Fin n, ∑ c : Fin l → Fin m, (if IsCopy H A r c then 1 else 0)
      ≤ ∑ _r : Fin k → Fin n, ∑ _c : Fin l → Fin m, 1 := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun c _ => ?_
        split <;> omega
    _ = n ^ k * m ^ l := by simp

end CopyCount

/-! ## E. Cardinalities of index-map spaces -/

theorem card_fun_fin {k n : ℕ} : Fintype.card (Fin k → Fin n) = n ^ k := by simp

/-- The number of `p`-tuples of rows of an `N × N` host is `N^p`. -/
theorem card_arrow_fin {p N : ℕ} : Fintype.card (Fin p → Fin N) = N ^ p := by simp




open Classical

/-! ## F. Assembling and splitting copies of `blockDiag H Z`

`[H 0; 0 Z]` has `0` in its two mixed blocks, so when a copy's rows and columns are split into
old and new parts, only the old-old and new-new entries carry information; the mixed entries
must vanish in the target.  These lemmas are the `Fin.append` bookkeeping for that. -/

section Copy

variable {k l p q n m : ℕ}

theorem isCopy_iff {H : BMat k l} {A : BMat n m} {r : Fin k → Fin n} {c : Fin l → Fin m} :
    IsCopy H A r c ↔ StrictMono r ∧ StrictMono c ∧ ∀ i j, A (r i) (c j) = H i j := Iff.rfl

theorem IsCopy.strictMono_rows {H : BMat k l} {A : BMat n m} {r : Fin k → Fin n}
    {c : Fin l → Fin m} (h : IsCopy H A r c) : StrictMono r := h.1

theorem IsCopy.strictMono_cols {H : BMat k l} {A : BMat n m} {r : Fin k → Fin n}
    {c : Fin l → Fin m} (h : IsCopy H A r c) : StrictMono c := h.2.1

theorem IsCopy.apply {H : BMat k l} {A : BMat n m} {r : Fin k → Fin n} {c : Fin l → Fin m}
    (h : IsCopy H A r c) (i : Fin k) (j : Fin l) : A (r i) (c j) = H i j := h.2.2 i j

theorem strictMono_castAdd_comp {k p n : ℕ} {r : Fin k → Fin n} (hr : StrictMono r) :
    StrictMono fun i => Fin.castAdd p (r i) := by
  intro a b hab
  rw [castAdd_lt_castAdd_iff]
  exact hr hab

theorem strictMono_natAdd_comp {k p : ℕ} {ρ : Fin k → Fin p} (hρ : StrictMono ρ) (n : ℕ) :
    StrictMono fun j => Fin.natAdd n (ρ j) := by
  intro a b hab
  rw [natAdd_lt_natAdd_iff]
  exact hρ hab

/-- Rows of the assembled copy: the old rows, then the new ones. -/
abbrev glueRows (p n : ℕ) {k : ℕ} (r : Fin k → Fin n) (ρ : Fin p → Fin p) :
    Fin (k + p) → Fin (n + p) :=
  Fin.append (fun i => Fin.castAdd p (r i)) (fun j => Fin.natAdd n (ρ j))

/-- Columns of the assembled copy: the old columns, then the new ones. -/
abbrev glueCols (q m : ℕ) {l : ℕ} (c : Fin l → Fin m) (γ : Fin q → Fin q) :
    Fin (l + q) → Fin (m + q) :=
  Fin.append (fun i => Fin.castAdd q (c i)) (fun j => Fin.natAdd m (γ j))

/-- **Assembling a copy of `[H 0; 0 Z]`.**  If the old rows/columns match `H`, the new
rows/columns match `Z`, and the two mixed blocks vanish in the target, the glued index maps
carry a copy of `[H 0; 0 Z]`.  This is the Claim of Step 3 and the forward half of Step 1. -/
theorem isCopy_of_parts {H : BMat k l} {Z : BMat p q} {B : BMat (n + p) (m + q)}
    {r : Fin k → Fin n} {c : Fin l → Fin m} {ρ : Fin p → Fin p} {γ : Fin q → Fin q}
    (hr : StrictMono r) (hc : StrictMono c) (hρ : StrictMono ρ) (hγ : StrictMono γ)
    (hoo : ∀ i j, B (Fin.castAdd p (r i)) (Fin.castAdd q (c j)) = H i j)
    (hon : ∀ i j, B (Fin.castAdd p (r i)) (Fin.natAdd m (γ j)) = false)
    (hno : ∀ i j, B (Fin.natAdd n (ρ i)) (Fin.castAdd q (c j)) = false)
    (hnn : ∀ i j, B (Fin.natAdd n (ρ i)) (Fin.natAdd m (γ j)) = Z i j) :
    IsCopy (blockDiag H Z) B (glueRows p n r ρ) (glueCols q m c γ) := by
  refine ⟨?_, ?_, fun i j => ?_⟩
  · exact strictMono_append (strictMono_castAdd_comp hr) (strictMono_natAdd_comp hρ n)
      (fun _ _ => castAdd_lt_natAdd _ _)
  · exact strictMono_append (strictMono_castAdd_comp hc) (strictMono_natAdd_comp hγ m)
      (fun _ _ => castAdd_lt_natAdd _ _)
  · obtain ⟨i', rfl⟩ | ⟨i', rfl⟩ := eq_castAdd_or_natAdd i
    · obtain ⟨j', rfl⟩ | ⟨j', rfl⟩ := eq_castAdd_or_natAdd j
      · rw [glueRows, glueCols, Fin.append_left, Fin.append_left,
          blockDiag_castAdd_castAdd, hoo]
      · rw [glueRows, glueCols, Fin.append_left, Fin.append_right,
          blockDiag_castAdd_natAdd, hon]
    · obtain ⟨j', rfl⟩ | ⟨j', rfl⟩ := eq_castAdd_or_natAdd j
      · rw [glueRows, glueCols, Fin.append_right, Fin.append_left,
          blockDiag_natAdd_castAdd, hno]
      · rw [glueRows, glueCols, Fin.append_right, Fin.append_right,
          blockDiag_natAdd_natAdd, hnn]

/-- Same, specialised to the block-diagonal target `[A 0; 0 Z']`: the mixed-block hypotheses
are then automatic. -/
theorem isCopy_blockDiag_append {H : BMat k l} {Z Z' : BMat p q} {A : BMat n m}
    {r : Fin k → Fin n} {c : Fin l → Fin m} {ρ : Fin p → Fin p} {γ : Fin q → Fin q}
    (hr : StrictMono r) (hc : StrictMono c) (hρ : StrictMono ρ) (hγ : StrictMono γ)
    (he : ∀ i j, A (r i) (c j) = H i j) (hZ : ∀ i j, Z' (ρ i) (γ j) = Z i j) :
    IsCopy (blockDiag H Z) (blockDiag A Z') (glueRows p n r ρ) (glueCols q m c γ) := by
  refine isCopy_of_parts hr hc hρ hγ ?_ ?_ ?_ ?_
  · intro i j; rw [blockDiag_castAdd_castAdd]; exact he i j
  · intro i j; rw [blockDiag_castAdd_natAdd]
  · intro i j; rw [blockDiag_natAdd_castAdd]
  · intro i j; rw [blockDiag_natAdd_natAdd]; exact hZ i j

end Copy

/-! ## G. `Free` and `Contains` -/

theorem contains_of_isCopy {H : BMat k l} {A : BMat n m} {r : Fin k → Fin n} {c : Fin l → Fin m}
    (h : IsCopy H A r c) : Contains H A := ⟨r, c, h⟩

theorem not_contains_iff {H : BMat k l} {A : BMat n m} :
    ¬ Contains H A ↔ ∀ r c, ¬ IsCopy H A r c := by
  constructor
  · rintro h r c hc; exact h ⟨r, c, hc⟩
  · rintro h ⟨r, c, hc⟩; exact h r c hc

theorem free_iff {H : BMat k l} {A : BMat n m} : Free H A ↔ ∀ r c, ¬ IsCopy H A r c :=
  not_contains_iff

theorem free_of_no_copy {H : BMat k l} {A : BMat n m} (h : ∀ r c, ¬ IsCopy H A r c) : Free H A :=
  free_iff.mpr h




open Classical

/-! ## H. The "pick one row from each group" space

Step 3 of the paper averages over the `(q*n)^p` ways of picking one new row out of each of the
`p` row groups, and the `(p*n)^q` ways of picking one new column out of each of the `q` column
groups.  This section identifies that pick space with `Fin p → Fin (q*n)` (resp.
`Fin q → Fin (p*n)`) and counts it, and records that such a pick is automatically strictly
increasing (an index in a later group is larger than any index in an earlier one).

Everything here is stated for the row/column index sets of `blowup Z n`, i.e.
`Fin (p * q * n)`. -/

section RowPick

variable {p q n : ℕ}

/-- A row pick: one index out of each row group of `blowup Z n`. -/
def RowPick (p q n : ℕ) : Type :=
  {f : Fin p → Fin (p * q * n) // ∀ a, (f a).val / (q * n) = a.val}

instance (p q n : ℕ) : Fintype (RowPick p q n) := by unfold RowPick; infer_instance

theorem rowPick_mem {f : Fin p → Fin (p * q * n)} (hf : ∀ a, (f a).val / (q * n) = a.val) :
    ⟨f, hf⟩ ∈ (Finset.univ : Finset (RowPick p q n)) := Finset.mem_univ _

/-- Indices in different row groups are ordered by their groups: a pick is already strictly
increasing, so no monotonicity constraint has to be imposed on it. -/
theorem rowPick_strictMono (hn : 0 < q * n) {f : Fin p → Fin (p * q * n)}
    (hf : ∀ a, (f a).val / (q * n) = a.val) : StrictMono f := by
  intro a b hab
  rw [Fin.lt_def]
  have h1 : (f a).val < (a.val + 1) * (q * n) := by
    rw [← Nat.div_lt_iff_lt_mul hn, hf a]
    omega
  have h2 : b.val * (q * n) ≤ (f b).val := by
    rw [← Nat.le_div_iff_mul_le hn, hf b]
  have h3 : (a.val + 1) * (q * n) ≤ b.val * (q * n) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem colPick_strictMono (hn : 0 < p * n) {g : Fin q → Fin (p * q * n)}
    (hg : ∀ a, (g a).val / (p * n) = a.val) : StrictMono g := by
  intro a b hab
  rw [Fin.lt_def]
  have h1 : (g a).val < (a.val + 1) * (p * n) := by
    rw [← Nat.div_lt_iff_lt_mul hn, hg a]
    omega
  have h2 : b.val * (p * n) ≤ (g b).val := by
    rw [← Nat.le_div_iff_mul_le hn, hg b]
  have h3 : (a.val + 1) * (p * n) ≤ b.val * (p * n) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The pick space is `Fin p → Fin (q*n)`: the offset inside the group is all that is free. -/
def rowPickEquiv (hn : 0 < q * n) :
    (Fin p → Fin (q * n)) ≃ RowPick p q n where
  toFun t := ⟨fun a => rowRep a (t a), fun a => rowRep_group hn a (t a)⟩
  invFun f := fun a => ⟨(f.1 a).val % (q * n), Nat.mod_lt _ hn⟩
  left_inv t := by
    funext a
    apply Fin.ext
    show (rowRep a (t a)).val % (q * n) = (t a).val
    rw [rowRep_val, Nat.mul_comm (a.val) (q * n), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (t a).isLt]
  right_inv f := by
    obtain ⟨f, hf⟩ := f
    apply Subtype.ext
    funext a
    apply Fin.ext
    show (rowRep a ⟨(f a).val % (q * n), _⟩).val = (f a).val
    rw [rowRep_val]
    show a.val * (q * n) + (f a).val % (q * n) = (f a).val
    rw [← hf a, Nat.mul_comm ((f a).val / (q * n)) (q * n), Nat.div_add_mod]

/-- The number of ways to pick one row from each of the `p` row groups of `blowup Z n`. -/
theorem rowPick_card (hn : 0 < q * n) :
    Fintype.card (RowPick p q n) = (q * n) ^ p := by
  rw [Fintype.card_congr (rowPickEquiv (n := n) hn).symm, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- A column pick: one index out of each column group of `blowup Z n`. -/
def ColPick (p q n : ℕ) : Type :=
  {g : Fin q → Fin (p * q * n) // ∀ b, (g b).val / (p * n) = b.val}

instance (p q n : ℕ) : Fintype (ColPick p q n) := by unfold ColPick; infer_instance

def colPickEquiv (hn : 0 < p * n) :
    (Fin q → Fin (p * n)) ≃ ColPick p q n where
  toFun t := ⟨fun b => colRep b (t b), fun b => colRep_group hn b (t b)⟩
  invFun f := fun b => ⟨(f.1 b).val % (p * n), Nat.mod_lt _ hn⟩
  left_inv t := by
    funext b
    apply Fin.ext
    show (colRep b (t b)).val % (p * n) = (t b).val
    rw [colRep_val, Nat.mul_comm (b.val) (p * n), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (t b).isLt]
  right_inv f := by
    obtain ⟨f, hf⟩ := f
    apply Subtype.ext
    funext b
    apply Fin.ext
    show (colRep b ⟨(f b).val % (p * n), _⟩).val = (f b).val
    rw [colRep_val]
    show b.val * (p * n) + (f b).val % (p * n) = (f b).val
    rw [← hf b, Nat.mul_comm ((f b).val / (p * n)) (p * n), Nat.div_add_mod]

/-- The number of ways to pick one column from each of the `q` column groups. -/
theorem colPick_card (hn : 0 < p * n) :
    Fintype.card (ColPick p q n) = (p * n) ^ q := by
  rw [Fintype.card_congr (colPickEquiv (n := n) hn).symm, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

end RowPick



/-! ## 2. Two sanity lemmas from §2 that Step 3 needs -/

theorem free_zero {k l n m : ℕ} (H : BMat k l) (h : ∃ i j, H i j = true) :
    Free H (zeros n m) := by
  rintro ⟨r, c, -, -, hpat⟩
  obtain ⟨i, j, hij⟩ := h
  have h1 := hpat i j
  simp only [zeros] at h1
  rw [hij] at h1
  exact Bool.false_ne_true h1

theorem editDist_le {k l n m : ℕ} (H : BMat k l) (A B : BMat n m) (hB : Free H B) :
    editDist H A ≤ hamming A B :=
  Nat.sInf_le ⟨B, hB, rfl⟩

theorem editDist_le_zero {k l n m : ℕ} (H : BMat k l) (A : BMat n m) (h : ∃ i j, H i j = true) :
    editDist H A ≤ n * m := by
  refine le_trans (editDist_le H A (zeros n m) (free_zero H h)) ?_
  simp only [hamming]
  calc (Finset.univ.filter (fun x : Fin n × Fin m =>
        A x.1 x.2 ≠ zeros n m x.1 x.2)).card
      ≤ (Finset.univ : Finset (Fin n × Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n * m := by simp [Finset.card_univ, Fintype.card_prod]

/-! ## 3. The `Fin`/`blockDiag`/`blowup` API used by the argument -/

@[simp] lemma blockDiag_old_old {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) (i : Fin k)
    (j : Fin l) : blockDiag H Z (Fin.castAdd p i) (Fin.castAdd q j) = H i j := by
  simp [blockDiag]

@[simp] lemma blockDiag_old_new {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) (i : Fin k)
    (j : Fin q) : blockDiag H Z (Fin.castAdd p i) (Fin.natAdd l j) = false := by
  simp [blockDiag]

@[simp] lemma blockDiag_new_old {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) (i : Fin p)
    (j : Fin l) : blockDiag H Z (Fin.natAdd k i) (Fin.castAdd q j) = false := by
  simp [blockDiag]

@[simp] lemma blockDiag_new_new {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) (i : Fin p)
    (j : Fin q) : blockDiag H Z (Fin.natAdd k i) (Fin.natAdd l j) = Z i j := by
  simp [blockDiag]

lemma fin_eq_natAdd_of_le {k p : ℕ} {z : Fin (k + p)} (hz : k ≤ (z : ℕ)) :
    ∃ w : Fin p, z = Fin.natAdd k w := by
  refine ⟨⟨(z : ℕ) - k, by omega⟩, ?_⟩
  ext
  simp only [Fin.val_natAdd]
  omega

lemma fin_eq_castAdd_of_lt {k p : ℕ} {z : Fin (k + p)} (hz : (z : ℕ) < k) :
    ∃ v : Fin k, z = Fin.castAdd p v :=
  ⟨_, (Fin.castAdd_castLT p z hz).symm⟩

lemma strictMono_addCases {k p : ℕ} {α : Type*} [LinearOrder α] (a : Fin k → α) (b : Fin p → α)
    (ha : StrictMono a) (hb : StrictMono b) (hab : ∀ i j, a i < b j) :
    StrictMono (Fin.addCases (motive := fun _ => α) (fun i => a i) (fun j => b j)) := by
  intro x y hxy
  rcases lt_or_ge (x : ℕ) k with hx | hx
  · obtain ⟨x', rfl⟩ := fin_eq_castAdd_of_lt (p := p) hx
    rcases lt_or_ge (y : ℕ) k with hy | hy
    · obtain ⟨y', rfl⟩ := fin_eq_castAdd_of_lt (p := p) hy
      simp only [Fin.addCases_left]
      exact ha (by rw [Fin.lt_def] at hxy ⊢; simpa using hxy)
    · obtain ⟨y', rfl⟩ := fin_eq_natAdd_of_le (k := k) hy
      simp only [Fin.addCases_left, Fin.addCases_right]
      exact hab _ _
  · obtain ⟨x', rfl⟩ := fin_eq_natAdd_of_le (k := k) hx
    rcases lt_or_ge (y : ℕ) k with hy | hy
    · rw [Fin.lt_def, Fin.val_natAdd] at hxy
      omega
    · obtain ⟨y', rfl⟩ := fin_eq_natAdd_of_le (k := k) hy
      simp only [Fin.addCases_right]
      refine hb (show x' < y' from ?_)
      rw [Fin.lt_def] at hxy ⊢
      simp only [Fin.val_natAdd] at hxy
      omega

/-! ## 4. Where the entries of `A⁺ = blockDiag A (blowup Z n)` sit

The big matrix has size `n + p*q*n`.  Its first `n` rows/columns are the *old* ones; the rest are
the *new* ones, indexed by `Fin (p*q*n)`.  New row `i` of `Z` corresponds to the block
`[i*(q*n), (i+1)*(q*n))` of new rows, new column `j` to `[j*(p*n), (j+1)*(p*n))`. -/

/-- The `v`-th new row inside row-group `i`. -/
def pickRow {p q n : ℕ} (i : Fin p) (v : Fin (q * n)) : Fin (p * q * n) :=
  ⟨i.val * (q * n) + v.val, by
    have h2 : v.val < q * n := v.isLt
    have h1 : i.val + 1 ≤ p := i.isLt
    have he : (i.val + 1) * (q * n) = i.val * (q * n) + q * n := Nat.succ_mul _ _
    have hmul : (i.val + 1) * (q * n) ≤ p * (q * n) := Nat.mul_le_mul_right _ h1
    have hlt : i.val * (q * n) + v.val < p * (q * n) := by omega
    have hassoc : p * (q * n) = p * q * n := by ring
    omega⟩

/-- The `w`-th new column inside column-group `j`. -/
def pickCol {p q n : ℕ} (j : Fin q) (w : Fin (p * n)) : Fin (p * q * n) :=
  ⟨j.val * (p * n) + w.val, by
    have h2 : w.val < p * n := w.isLt
    have h1 : j.val + 1 ≤ q := j.isLt
    have he : (j.val + 1) * (p * n) = j.val * (p * n) + p * n := Nat.succ_mul _ _
    have hmul : (j.val + 1) * (p * n) ≤ q * (p * n) := Nat.mul_le_mul_right _ h1
    have hlt : j.val * (p * n) + w.val < q * (p * n) := by omega
    have hassoc : q * (p * n) = p * q * n := by ring
    omega⟩

/-- A pick: one new row in each row group and one new column in each column group. -/
abbrev Pick (p q n : ℕ) := (Fin p → Fin (q * n)) × (Fin q → Fin (p * n))

section PickAPI

variable {p q n : ℕ}

@[simp] lemma pickRow_val (i : Fin p) (v : Fin (q * n)) :
    (pickRow i v : ℕ) = i.val * (q * n) + v.val := rfl

@[simp] lemma pickCol_val (j : Fin q) (w : Fin (p * n)) :
    (pickCol j w : ℕ) = j.val * (p * n) + w.val := rfl

lemma pickRow_div (i : Fin p) (v : Fin (q * n)) :
    (pickRow i v : ℕ) / (q * n) = i.val := by
  have hpos : 0 < q * n := lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hx : ((q * n) * i.val + v.val) / (q * n) = i.val + v.val / (q * n) :=
    Nat.mul_add_div hpos i.val v.val
  have hmain : (pickRow i v : ℕ) = (q * n) * i.val + v.val := by
    simp only [pickRow_val]; ring
  have hy : v.val / (q * n) = 0 := Nat.div_eq_of_lt v.isLt
  rw [hmain, hx, hy]
  omega

lemma pickCol_div (j : Fin q) (w : Fin (p * n)) :
    (pickCol j w : ℕ) / (p * n) = j.val := by
  have hpos : 0 < p * n := lt_of_le_of_lt (Nat.zero_le _) w.isLt
  have hx : ((p * n) * j.val + w.val) / (p * n) = j.val + w.val / (p * n) :=
    Nat.mul_add_div hpos j.val w.val
  have hmain : (pickCol j w : ℕ) = (p * n) * j.val + w.val := by
    simp only [pickCol_val]; ring
  have hy : w.val / (p * n) = 0 := Nat.div_eq_of_lt w.isLt
  rw [hmain, hx, hy]
  omega

/-- The `(i,j)` entry of the blowup, read at the corresponding picked rows/columns, is `Z i j`. -/
lemma blowup_pick (Z : BMat p q) (i : Fin p) (v : Fin (q * n)) (j : Fin q) (w : Fin (p * n)) :
    blowup Z n (pickRow i v) (pickCol j w) = Z i j := by
  have h1 := pickRow_div i v
  have h2 := pickCol_div j w
  simp only [blowup, h1, h2]

lemma pickRow_lt_succ (i : Fin p) (v : Fin (q * n)) :
    (pickRow i v : ℕ) < (i.val + 1) * (q * n) := by
  have he : (i.val + 1) * (q * n) = i.val * (q * n) + q * n := Nat.succ_mul _ _
  have h2 : v.val < q * n := v.isLt
  simp only [pickRow_val]
  omega

lemma pickCol_lt_succ (j : Fin q) (w : Fin (p * n)) :
    (pickCol j w : ℕ) < (j.val + 1) * (p * n) := by
  have he : (j.val + 1) * (p * n) = j.val * (p * n) + p * n := Nat.succ_mul _ _
  have h2 : w.val < p * n := w.isLt
  simp only [pickCol_val]
  omega

lemma pickRow_lt_of_lt {i i' : Fin p} (h : i < i') (v : Fin (q * n)) (v' : Fin (q * n)) :
    pickRow i v < pickRow i' v' := by
  have h1 : (pickRow i v : ℕ) < (i.val + 1) * (q * n) := pickRow_lt_succ i v
  have h2 : (i.val + 1) * (q * n) ≤ i'.val * (q * n) :=
    Nat.mul_le_mul_right _ (by rw [Fin.lt_def] at h; omega)
  have h3 : (pickRow i' v' : ℕ) = i'.val * (q * n) + v'.val := rfl
  rw [Fin.lt_def]
  omega

lemma pickCol_lt_of_lt {j j' : Fin q} (h : j < j') (w : Fin (p * n)) (w' : Fin (p * n)) :
    pickCol j w < pickCol j' w' := by
  have h1 : (pickCol j w : ℕ) < (j.val + 1) * (p * n) := pickCol_lt_succ j w
  have h2 : (j.val + 1) * (p * n) ≤ j'.val * (p * n) :=
    Nat.mul_le_mul_right _ (by rw [Fin.lt_def] at h; omega)
  have h3 : (pickCol j' w' : ℕ) = j'.val * (p * n) + w'.val := rfl
  rw [Fin.lt_def]
  omega

lemma pickRow_pair_inj {i i' : Fin p} {v v' : Fin (q * n)} (h : pickRow i v = pickRow i' v') :
    i = i' ∧ v = v' := by
  have hv : (pickRow i v : ℕ) = (pickRow i' v' : ℕ) := by rw [h]
  have hd1 := pickRow_div i v
  have hd2 := pickRow_div i' v'
  have hdiv : (pickRow i v : ℕ) / (q * n) = (pickRow i' v' : ℕ) / (q * n) := by rw [hv]
  have hi : i = i' := Fin.ext (by omega)
  have hvv : v = v' := by
    have h1 : (pickRow i v : ℕ) = i.val * (q * n) + v.val := rfl
    have h2 : (pickRow i' v' : ℕ) = i'.val * (q * n) + v'.val := rfl
    have hii : i.val * (q * n) = i'.val * (q * n) := by rw [hi]
    exact Fin.ext (by omega)
  exact ⟨hi, hvv⟩

lemma pickRow_injective : Function.Injective (fun x : Fin p × Fin (q * n) => pickRow x.1 x.2) :=
  fun a b h => by
  obtain ⟨h1, h2⟩ := pickRow_pair_inj (i := a.1) (i' := b.1) (v := a.2) (v' := b.2) h
  exact Prod.ext h1 h2

lemma pickCol_pair_inj {j j' : Fin q} {w w' : Fin (p * n)} (h : pickCol j w = pickCol j' w') :
    j = j' ∧ w = w' := by
  have hv : (pickCol j w : ℕ) = (pickCol j' w' : ℕ) := by rw [h]
  have hd1 := pickCol_div j w
  have hd2 := pickCol_div j' w'
  have hdiv : (pickCol j w : ℕ) / (p * n) = (pickCol j' w' : ℕ) / (p * n) := by rw [hv]
  have hj : j = j' := Fin.ext (by omega)
  have hww : w = w' := by
    have h1 : (pickCol j w : ℕ) = j.val * (p * n) + w.val := rfl
    have h2 : (pickCol j' w' : ℕ) = j'.val * (p * n) + w'.val := rfl
    have hjj : j.val * (p * n) = j'.val * (p * n) := by rw [hj]
    exact Fin.ext (by omega)
  exact ⟨hj, hww⟩

lemma pickCol_injective : Function.Injective (fun x : Fin q × Fin (p * n) => pickCol x.1 x.2) :=
  fun a b h => by
  obtain ⟨h1, h2⟩ := pickCol_pair_inj (j := a.1) (j' := b.1) (w := a.2) (w' := b.2) h
  exact Prod.ext h1 h2

lemma pickCol_eq_iff {j : Fin q} {w w' : Fin (p * n)} : pickCol j w = pickCol j w' ↔ w = w' := by
  constructor
  · intro h
    exact (pickCol_pair_inj h).2
  · intro h
    rw [h]

/-- Old rows: `Fin n → Fin (n + p*q*n)`. -/
abbrev oldRow (n : ℕ) (p q : ℕ) (r : Fin n) : Fin (n + p * q * n) := Fin.castAdd (p * q * n) r

/-- New rows, as indices of the big matrix. -/
abbrev newIdx (n : ℕ) (p q : ℕ) (c : Fin (p * q * n)) : Fin (n + p * q * n) :=
  Fin.natAdd n c

lemma oldRow_lt_newIdx (r : Fin n) (c : Fin (p * q * n)) :
    oldRow n p q r < newIdx n p q c := by
  rw [Fin.lt_def]
  simp only [oldRow, newIdx, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- The `i`-th picked new row of the pick `x`. -/
abbrev pickRowN (x : Pick p q n) (i : Fin p) : Fin (n + p * q * n) :=
  newIdx n p q (pickRow i (x.1 i))

/-- The `j`-th picked new column of the pick `x`. -/
abbrev pickColN (x : Pick p q n) (j : Fin q) : Fin (n + p * q * n) :=
  newIdx n p q (pickCol j (x.2 j))

lemma strictMono_pickRow (x : Pick p q n) : StrictMono (fun i => pickRow i (x.1 i)) := by
  intro i i' h
  have h1 : (pickRow i (x.1 i) : ℕ) < (i.val + 1) * (q * n) := pickRow_lt_succ i _
  have h2 : (i.val + 1) * (q * n) ≤ i'.val * (q * n) :=
    Nat.mul_le_mul_right _ (by rw [Fin.lt_def] at h; omega)
  have h3 : (pickRow i' (x.1 i') : ℕ) = i'.val * (q * n) + (x.1 i').val := rfl
  rw [Fin.lt_def]
  change (pickRow i (x.1 i) : ℕ) < (pickRow i' (x.1 i') : ℕ)
  omega

lemma strictMono_pickCol (x : Pick p q n) : StrictMono (fun j => pickCol j (x.2 j)) := by
  intro j j' h
  have h1 : (pickCol j (x.2 j) : ℕ) < (j.val + 1) * (p * n) := pickCol_lt_succ j _
  have h2 : (j.val + 1) * (p * n) ≤ j'.val * (p * n) :=
    Nat.mul_le_mul_right _ (by rw [Fin.lt_def] at h; omega)
  have h3 : (pickCol j' (x.2 j') : ℕ) = j'.val * (p * n) + (x.2 j').val := rfl
  rw [Fin.lt_def]
  change (pickCol j (x.2 j) : ℕ) < (pickCol j' (x.2 j') : ℕ)
  omega

lemma strictMono_pickRowN (x : Pick p q n) : StrictMono (pickRowN (p := p) (q := q) (n := n) x) := by
  intro i i' h
  exact Fin.strictMono_natAdd n (strictMono_pickRow x h)

lemma strictMono_pickColN (x : Pick p q n) : StrictMono (pickColN (p := p) (q := q) (n := n) x) := by
  intro j j' h
  exact Fin.strictMono_natAdd n (strictMono_pickCol x h)

lemma strictMono_oldRow : StrictMono (oldRow n p q : Fin n → Fin (n + p * q * n)) :=
  Fin.strictMono_castAdd (p * q * n)

@[simp] lemma blockDiag_oldRow_oldRow (A : BMat n n) (Z : BMat p q) (r c : Fin n) :
    blockDiag A (blowup Z n) (oldRow n p q r) (oldRow n p q c) = A r c :=
  blockDiag_old_old A (blowup Z n) r c

@[simp] lemma blockDiag_oldRow_newIdx (A : BMat n n) (Z : BMat p q) (r : Fin n)
    (c : Fin (p * q * n)) : blockDiag A (blowup Z n) (oldRow n p q r) (newIdx n p q c) = false :=
  blockDiag_old_new A (blowup Z n) r c

@[simp] lemma blockDiag_newIdx_oldRow (A : BMat n n) (Z : BMat p q) (r : Fin (p * q * n))
    (c : Fin n) : blockDiag A (blowup Z n) (newIdx n p q r) (oldRow n p q c) = false :=
  blockDiag_new_old A (blowup Z n) r c

@[simp] lemma blockDiag_newIdx_newIdx (A : BMat n n) (Z : BMat p q)
    (r c : Fin (p * q * n)) : blockDiag A (blowup Z n) (newIdx n p q r) (newIdx n p q c)
      = blowup Z n r c :=
  blockDiag_new_new A (blowup Z n) r c

end PickAPI

/-! ## 5. The pick, its bad lines, and the corrected old-old block -/

section Step3

variable {k l p q n : ℕ}

/-- Row `r` (old) is *bad* for the pick `x`: `B` has a `1` in it at a picked new column.  Since
`A⁺` has a `0` there, every bad row accounts for a change in the mixed block. -/
def badRow (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) (r : Fin n) : Prop :=
  ∃ j : Fin q, B (oldRow n p q r) (pickColN x j) = true

/-- Column `c` (old) is *bad* for the pick `x`: `B` has a `1` in it at a picked new row. -/
def badCol (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) (c : Fin n) : Prop :=
  ∃ i : Fin p, B (pickRowN x i) (oldRow n p q c) = true

/-- The old-old block of `B`, with all bad rows and bad columns replaced by zeros. -/
noncomputable def Bcirc (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) :
    BMat n n :=
  fun r c => if badRow B x r ∨ badCol B x c then false else B (oldRow n p q r) (oldRow n p q c)

/-- A pick is *good* if `B` agrees with `Z` on all `p*q` picked new-new entries. -/
def Good (Z : BMat p q) (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) : Prop :=
  ∀ (i : Fin p) (j : Fin q), B (pickRowN x i) (pickColN x j) = Z i j

lemma fin_or_castAdd_natAdd {a b : ℕ} (z : Fin (a + b)) :
    (∃ v : Fin a, z = Fin.castAdd b v) ∨ (∃ w : Fin b, z = Fin.natAdd a w) := by
  by_cases h : (z : ℕ) < a
  · exact Or.inl (fin_eq_castAdd_of_lt h)
  · exact Or.inr (fin_eq_natAdd_of_le (by omega))

/-- **Step 3, the key claim.**  If the pick is good and `B` has no copy of `H' = blockDiag H Z`,
then the corrected old-old block `B°` has no copy of `H`.

Copying the paper: a copy of `H` in `B°` cannot use a zeroed row or column, because every row and
every column of `H` contains a `1`; adding the `p` picked rows and the `q` picked columns to it
then gives a copy of `H'` in `B`. -/
theorem good_free (H : BMat k l) (hH : NoZeroLine H) (Z : BMat p q)
    (B : BMat (n + p * q * n) (n + p * q * n)) (hB : Free (blockDiag H Z) B)
    (x : Pick p q n) (hgood : Good Z B x) : Free H (Bcirc B x) := by
  rintro ⟨r, c, hr, hc, hpat⟩
  have hrowFalse : ∀ a, ¬ badRow B x (r a) := by
    intro a hbad
    obtain ⟨b0, hb0⟩ := hH.1 a
    have h1 : Bcirc B x (r a) (c b0) = H a b0 := hpat a b0
    unfold Bcirc at h1
    rw [if_pos (Or.inl hbad)] at h1
    rw [hb0] at h1
    exact Bool.false_ne_true h1
  have hcolFalse : ∀ b, ¬ badCol B x (c b) := by
    intro b hbad
    obtain ⟨a0, ha0⟩ := hH.2 b
    have h1 : Bcirc B x (r a0) (c b) = H a0 b := hpat a0 b
    unfold Bcirc at h1
    rw [if_pos (Or.inr hbad)] at h1
    rw [ha0] at h1
    exact Bool.false_ne_true h1
  have hpat' : ∀ a b, B (oldRow n p q (r a)) (oldRow n p q (c b)) = H a b := by
    intro a b
    have h1 : Bcirc B x (r a) (c b) = H a b := hpat a b
    have hnot : ¬ (badRow B x (r a) ∨ badCol B x (c b)) := not_or.2 ⟨hrowFalse a, hcolFalse b⟩
    unfold Bcirc at h1
    rw [if_neg hnot] at h1
    exact h1
  have hmix1 : ∀ a j, B (oldRow n p q (r a)) (pickColN x j) = false := by
    intro a j
    cases hBv : B (oldRow n p q (r a)) (pickColN x j) with
    | false => rfl
    | true => exact absurd ⟨j, hBv⟩ (hrowFalse a)
  have hmix2 : ∀ i b, B (pickRowN x i) (oldRow n p q (c b)) = false := by
    intro i b
    cases hBv : B (pickRowN x i) (oldRow n p q (c b)) with
    | false => rfl
    | true => exact absurd ⟨i, hBv⟩ (hcolFalse b)
  refine hB ⟨Fin.addCases (motive := fun _ => Fin (n + p * q * n))
      (fun i => oldRow n p q (r i)) (fun j => pickRowN x j),
    Fin.addCases (motive := fun _ => Fin (n + p * q * n))
      (fun i => oldRow n p q (c i)) (fun j => pickColN x j), ?_, ?_, ?_⟩
  · refine strictMono_addCases _ _ (strictMono_oldRow.comp hr) (strictMono_pickRowN x) ?_
    intro i j
    exact oldRow_lt_newIdx _ _
  · refine strictMono_addCases _ _ (strictMono_oldRow.comp hc) (strictMono_pickColN x) ?_
    intro i j
    exact oldRow_lt_newIdx _ _
  · intro i j
    rcases fin_or_castAdd_natAdd (a := k) (b := p) i with ⟨i', rfl⟩ | ⟨i', rfl⟩
    · rcases fin_or_castAdd_natAdd (a := l) (b := q) j with ⟨j', rfl⟩ | ⟨j', rfl⟩
      · rw [Fin.addCases_left, Fin.addCases_left, blockDiag_old_old]
        exact hpat' i' j'
      · rw [Fin.addCases_left, Fin.addCases_right, blockDiag_old_new]
        exact hmix1 i' j'
    · rcases fin_or_castAdd_natAdd (a := l) (b := q) j with ⟨j', rfl⟩ | ⟨j', rfl⟩
      · rw [Fin.addCases_right, Fin.addCases_left, blockDiag_new_old]
        exact hmix2 i' j'
      · rw [Fin.addCases_right, Fin.addCases_right, blockDiag_new_new]
        exact hgood i' j'

end Step3

/-! ## 6. Counting the four blocks of `A⁺` against `B` -/

section Blocks

variable {k l p q n : ℕ}

/-- The old-old block of `A` against `B`. -/
noncomputable def Eold (A : BMat n n) (B : BMat (n + p * q * n) (n + p * q * n)) : ℕ :=
  ∑ r : Fin n, ∑ c : Fin n,
    if A r c ≠ B (oldRow n p q r) (oldRow n p q c) then 1 else 0

/-- The old-row/new-column block: `A⁺` is `0` there, so a differing entry is a `1` of `B`. -/
noncomputable def E1a (B : BMat (n + p * q * n) (n + p * q * n)) : ℕ :=
  ∑ r : Fin n, ∑ c : Fin (p * q * n),
    if B (oldRow n p q r) (newIdx n p q c) = true then 1 else 0

/-- The new-row/old-column block. -/
noncomputable def E1b (B : BMat (n + p * q * n) (n + p * q * n)) : ℕ :=
  ∑ r : Fin (p * q * n), ∑ c : Fin n,
    if B (newIdx n p q r) (oldRow n p q c) = true then 1 else 0

/-- The new-new block. -/
noncomputable def E2 (Z : BMat p q) (B : BMat (n + p * q * n) (n + p * q * n)) : ℕ :=
  ∑ r : Fin (p * q * n), ∑ c : Fin (p * q * n),
    if blowup Z n r c ≠ B (newIdx n p q r) (newIdx n p q c) then 1 else 0

lemma false_ne_iff (b : Bool) : (false ≠ b) ↔ b = true := by cases b <;> simp

lemma card_filter_eq_sum {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ x : α, if P x then 1 else 0 := by
  rw [Finset.card_filter]

/-- `hamming A⁺ B` is the sum of the four block counts. -/
theorem hamming_blockDiag_split (A : BMat n n) (Z : BMat p q)
    (B : BMat (n + p * q * n) (n + p * q * n)) :
    hamming (blockDiag A (blowup Z n)) B = Eold A B + E1a B + E1b B + E2 Z B := by
  have htot : hamming (blockDiag A (blowup Z n)) B
      = ∑ i : Fin (n + p * q * n), ∑ j : Fin (n + p * q * n),
          if blockDiag A (blowup Z n) i j ≠ B i j then 1 else 0 := by
    rw [hamming, card_filter_eq_sum, Fintype.sum_prod_type]
  rw [htot]
  rw [Fin.sum_univ_add]
  rw [Finset.sum_congr rfl
    (fun i _ => Fin.sum_univ_add (f := fun j => if blockDiag A (blowup Z n) (Fin.castAdd _ i) j ≠
      B (Fin.castAdd _ i) j then 1 else 0))]
  rw [Finset.sum_congr rfl
    (fun i _ => Fin.sum_univ_add (f := fun j => if blockDiag A (blowup Z n) (Fin.natAdd n i) j ≠
      B (Fin.natAdd n i) j then 1 else 0))]
  simp only [Finset.sum_add_distrib]
  have h0 : (∑ i : Fin n, ∑ j : Fin n,
      if blockDiag A (blowup Z n) (Fin.castAdd (p * q * n) i) (Fin.castAdd (p * q * n) j) ≠
        B (Fin.castAdd (p * q * n) i) (Fin.castAdd (p * q * n) j) then 1 else 0) = Eold A B := by
    simp only [Eold, oldRow, blockDiag_old_old]
  have h1 : (∑ i : Fin n, ∑ j : Fin (p * q * n),
      if blockDiag A (blowup Z n) (Fin.castAdd (p * q * n) i) (Fin.natAdd n j) ≠
        B (Fin.castAdd (p * q * n) i) (Fin.natAdd n j) then 1 else 0) = E1a B := by
    simp only [E1a, oldRow, newIdx, blockDiag_old_new, false_ne_iff]
  have h2 : (∑ i : Fin (p * q * n), ∑ j : Fin n,
      if blockDiag A (blowup Z n) (Fin.natAdd n i) (Fin.castAdd (p * q * n) j) ≠
        B (Fin.natAdd n i) (Fin.castAdd (p * q * n) j) then 1 else 0) = E1b B := by
    simp only [E1b, oldRow, newIdx, blockDiag_new_old, false_ne_iff]
  have h3 : (∑ i : Fin (p * q * n), ∑ j : Fin (p * q * n),
      if blockDiag A (blowup Z n) (Fin.natAdd n i) (Fin.natAdd n j) ≠
        B (Fin.natAdd n i) (Fin.natAdd n j) then 1 else 0) = E2 Z B := by
    simp only [E2, newIdx, blockDiag_new_new]
  rw [h0, h1, h2, h3]
  omega

end Blocks



theorem sub_lt_of_lt {a D n : ℕ} (hD : 0 < D) (h : a < n + D) : a - n < D := by
  rcases Nat.lt_or_ge a n with hlt | hge
  · rw [Nat.sub_eq_zero_of_le (le_of_lt hlt)]
    exact hD
  · exact Nat.sub_lt_left_of_lt_add hge h

/-- Removing `n` from the index of a new row. -/
theorem sub_lt_of_le {a D n : ℕ} (hge : n ≤ a) (h : a < n + D) : a - n < D :=
  Nat.sub_lt_left_of_lt_add hge h

/-! ## Same-group rows and columns of `blockDiag X (blowup Z n)` -/

/-- Two *new* rows of `blockDiag X (blowup Z n)` whose indices lie in the same row group of
`blowup Z n` are equal as functions. -/
theorem row_eq_of_group_eq {X : BMat n n} {Z : BMat p q} {a b : Fin (n + p * q * n)}
    (ha : n ≤ a.val) (hb : n ≤ b.val)
    (h : (a.val - n) / (q * n) = (b.val - n) / (q * n)) :
    blockDiag X (blowup Z n) a = blockDiag X (blowup Z n) b := by
  set a' : Fin (p * q * n) := ⟨a.val - n, sub_lt_of_le ha a.isLt⟩ with ha'
  set b' : Fin (p * q * n) := ⟨b.val - n, sub_lt_of_le hb b.isLt⟩ with hb'
  have hA : a = Fin.natAdd n a' := natAdd_of_val_ge ha
  have hB : b = Fin.natAdd n b' := natAdd_of_val_ge hb
  have hdiv : a'.val / (q * n) = b'.val / (q * n) := h
  rw [hA, hB]
  funext j
  exact blockDiag_blowup_row_congr X Z hdiv j

/-- Two *new* columns of `blockDiag X (blowup Z n)` whose indices lie in the same column group of
`blowup Z n` are equal as functions. -/
theorem col_eq_of_group_eq {X : BMat n n} {Z : BMat p q} {a b : Fin (n + p * q * n)}
    (ha : n ≤ a.val) (hb : n ≤ b.val)
    (h : (a.val - n) / (p * n) = (b.val - n) / (p * n)) :
    (fun i => blockDiag X (blowup Z n) i a) = fun i => blockDiag X (blowup Z n) i b := by
  set a' : Fin (p * q * n) := ⟨a.val - n, sub_lt_of_le ha a.isLt⟩ with ha'
  set b' : Fin (p * q * n) := ⟨b.val - n, sub_lt_of_le hb b.isLt⟩ with hb'
  have hA : a = Fin.natAdd n a' := natAdd_of_val_ge ha
  have hB : b = Fin.natAdd n b' := natAdd_of_val_ge hb
  have hdiv : a'.val / (p * n) = b'.val / (p * n) := h
  rw [hA, hB]
  funext j
  exact blockDiag_blowup_col_congr X Z hdiv j

/-- Group index of a new row, bounded by `p`. -/
theorem div_lt_p {a : Fin (n + p * q * n)} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) :
    (a.val - n) / (q * n) < p := by
  have hpos : 0 < p * q * n := by positivity
  have h2 : a.val - n < p * q * n := sub_lt_of_lt hpos a.isLt
  have h1 : a.val - n < (q * n) * p := by rw [show (q * n) * p = p * q * n by ring]; exact h2
  exact Nat.div_lt_of_lt_mul h1

/-- Group index of a new column, bounded by `q`. -/
theorem div_lt_q {a : Fin (n + p * q * n)} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) :
    (a.val - n) / (p * n) < q := by
  have hpos : 0 < p * q * n := by positivity
  have h2 : a.val - n < p * q * n := sub_lt_of_lt hpos a.isLt
  have h1 : a.val - n < (p * n) * q := by rw [show (p * n) * q = p * q * n by ring]; exact h2
  exact Nat.div_lt_of_lt_mul h1

/-! ## Step 1, row part -/

/-- **Step 1, rows.**  If `Z` has pairwise distinct rows, the `H`-rows of a copy of
`blockDiag H Z` in `blockDiag X (blowup Z n)` are old. -/
theorem step1_rows_old (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H)
    (hk : 0 < k) (hp : 0 < p) (hq : 0 < q) (hZ : Function.Injective Z)
    (X : BMat n n) {r : Fin (k + p) → Fin (n + p * q * n)}
    {c : Fin (l + q) → Fin (n + p * q * n)}
    (hr : StrictMono r)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j) :
    ∀ i : Fin k, (r (Fin.castAdd p i)).val < n := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro i
    exact absurd (r (Fin.castAdd p i)).isLt (by simp)
  -- `l` is positive, since row `0` of `H` has a `1`
  have hl : 0 < l := by
    obtain ⟨j, -⟩ := hH.1 ⟨0, hk⟩
    have := j.isLt
    omega
  -- the last `H`-row of `H'`
  set k' : Fin k := ⟨k - 1, by omega⟩ with hk'def
  by_contra hcon
  push_neg at hcon
  -- the last `H`-row of the copy is new
  have hlast_new : n ≤ (r (Fin.castAdd p k')).val := by
    obtain ⟨i₀, hi₀⟩ := hcon
    have hle : Fin.castAdd p i₀ ≤ Fin.castAdd p k' := by
      rw [castAdd_le_castAdd_iff]
      exact Fin.le_def.mpr (by simp only [hk'def, Fin.val_mk]; omega)
    have := hr.monotone hle
    rw [Fin.le_def] at this
    omega
  -- the `Z`-rows of the copy are new
  have hZrows_new : ∀ i : Fin p, n ≤ (r (Fin.natAdd k i)).val := by
    intro i
    have hlt : Fin.castAdd p k' < Fin.natAdd k i := castAdd_lt_natAdd k' i
    have := hr.monotone (le_of_lt hlt)
    rw [Fin.le_def] at this
    omega
  -- a `1` in the last `H`-row, and the column of the copy that carries it
  obtain ⟨j0, hj0⟩ := hH.1 k'
  have hcj0_new : n ≤ (c (Fin.castAdd q j0)).val := by
    by_contra hcol
    push_neg at hcol
    have h1 : blockDiag X (blowup Z n) (r (Fin.castAdd p k')) (c (Fin.castAdd q j0)) = true := by
      rw [hentry (Fin.castAdd p k') (Fin.castAdd q j0), blockDiag_castAdd_castAdd, hj0]
    rw [blockDiag_apply_new_old X (blowup Z n) hlast_new hcol] at h1
    exact Bool.false_ne_true h1
  -- group index of the `Z`-rows
  set γ : Fin p → ℕ := fun i => ((r (Fin.natAdd k i)).val - n) / (q * n) with hγ
  set γH : ℕ := ((r (Fin.castAdd p k')).val - n) / (q * n) with hγH
  have hγlt : ∀ i, γ i < p := fun i => div_lt_p (n := n) hn hp hq
  have hγHlt : γH < p := div_lt_p (n := n) hn hp hq
  by_cases hinj : Function.Injective γ
  · -- all `p` `Z`-rows lie in distinct groups, so they hit the group of the last `H`-row
    have himg : (Finset.univ.image γ).card = p := by
      rw [Finset.card_image_of_injOn (fun a _ b _ h => hinj h), Finset.card_univ, Fintype.card_fin]
    have hEq : Finset.univ.image γ = Finset.range p := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (hγlt i)
      · rw [himg, Finset.card_range]
    have hmem : γH ∈ Finset.univ.image γ := by
      rw [hEq]
      exact Finset.mem_range.mpr hγHlt
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have hrow := congrFun (row_eq_of_group_eq (Z := Z) (X := X) (hZrows_new i) hlast_new hi)
      (c (Fin.castAdd q j0))
    have h1 : blockDiag X (blowup Z n) (r (Fin.natAdd k i)) (c (Fin.castAdd q j0)) = false := by
      rw [hentry (Fin.natAdd k i) (Fin.castAdd q j0), blockDiag_natAdd_castAdd]
    have h2 : blockDiag X (blowup Z n) (r (Fin.castAdd p k')) (c (Fin.castAdd q j0)) = true := by
      rw [hentry (Fin.castAdd p k') (Fin.castAdd q j0), blockDiag_castAdd_castAdd, hj0]
    rw [h1, h2] at hrow
    exact Bool.false_ne_true hrow
  · -- two `Z`-rows lie in the same group
    obtain ⟨i, i', hgrp, hii'⟩ := Function.not_injective_iff.mp hinj
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (fun h : Z i = Z i' => hii' (hZ h))
    have hrow := congrFun (row_eq_of_group_eq (Z := Z) (X := X) (hZrows_new i) (hZrows_new i')
      hgrp) (c (Fin.natAdd l j))
    have h1 : blockDiag X (blowup Z n) (r (Fin.natAdd k i)) (c (Fin.natAdd l j)) = Z i j := by
      rw [hentry (Fin.natAdd k i) (Fin.natAdd l j), blockDiag_natAdd_natAdd]
    have h2 : blockDiag X (blowup Z n) (r (Fin.natAdd k i')) (c (Fin.natAdd l j)) = Z i' j := by
      rw [hentry (Fin.natAdd k i') (Fin.natAdd l j), blockDiag_natAdd_natAdd]
    rw [h1, h2] at hrow
    exact hj hrow

/-! ## Step 1, column part -/

/-- **Step 1, columns from rows.**  If all `H`-rows of the copy are old, then all `H`-columns
are. -/
theorem step1_cols_old_of_rows_old (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H)
    (hk : 0 < k) (X : BMat n n) {r : Fin (k + p) → Fin (n + p * q * n)}
    {c : Fin (l + q) → Fin (n + p * q * n)}
    (hc : StrictMono c)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j)
    (hrows : ∀ i : Fin k, (r (Fin.castAdd p i)).val < n) :
    ∀ j : Fin l, (c (Fin.castAdd q j)).val < n := by
  classical
  have hl : 0 < l := by
    obtain ⟨j, -⟩ := hH.1 ⟨0, hk⟩
    have := j.isLt
    omega
  set l' : Fin l := ⟨l - 1, by omega⟩ with hl'def
  have hlast : (c (Fin.castAdd q l')).val < n := by
    by_contra hnew
    push_neg at hnew
    obtain ⟨i0, hi0⟩ := hH.2 l'
    have h1 : blockDiag X (blowup Z n) (r (Fin.castAdd p i0)) (c (Fin.castAdd q l')) = true := by
      rw [hentry (Fin.castAdd p i0) (Fin.castAdd q l'), blockDiag_castAdd_castAdd, hi0]
    rw [blockDiag_apply_old_new X (blowup Z n) (hrows i0) hnew] at h1
    exact Bool.false_ne_true h1
  intro j
  have hle : Fin.castAdd q j ≤ Fin.castAdd q l' := by
    rw [castAdd_le_castAdd_iff]
    exact Fin.le_def.mpr (by simp only [hl'def, Fin.val_mk]; omega)
  have := hc.monotone hle
  rw [Fin.le_def] at this
  omega


/-! ## Step 1, the transposed row/column parts (for `Function.Injective` on the columns of `Z`) -/

/-- **Step 1, columns.**  If `Z` has pairwise distinct columns, the `H`-columns of a copy of
`blockDiag H Z` in `blockDiag X (blowup Z n)` are old. -/
theorem step1_cols_old (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H)
    (hk : 0 < k) (hp : 0 < p) (hq : 0 < q) (hZ : Function.Injective fun j i => Z i j)
    (X : BMat n n) {r : Fin (k + p) → Fin (n + p * q * n)}
    {c : Fin (l + q) → Fin (n + p * q * n)}
    (hc : StrictMono c)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j) :
    ∀ j : Fin l, (c (Fin.castAdd q j)).val < n := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro j
    exact absurd (c (Fin.castAdd q j)).isLt (by simp)
  have hl : 0 < l := by
    obtain ⟨j, -⟩ := hH.1 ⟨0, hk⟩
    have := j.isLt
    omega
  set l' : Fin l := ⟨l - 1, by omega⟩ with hl'def
  by_contra hcon
  push Not at hcon
  -- the last `H`-column of the copy is new
  have hlast_new : n ≤ (c (Fin.castAdd q l')).val := by
    obtain ⟨j₀, hj₀⟩ := hcon
    have hle : Fin.castAdd q j₀ ≤ Fin.castAdd q l' := by
      rw [castAdd_le_castAdd_iff]
      exact Fin.le_def.mpr (by simp only [hl'def, Fin.val_mk]; omega)
    have := hc.monotone hle
    rw [Fin.le_def] at this
    omega
  -- the `Z`-columns of the copy are new
  have hZcols_new : ∀ j : Fin q, n ≤ (c (Fin.natAdd l j)).val := by
    intro j
    have hlt : Fin.castAdd q l' < Fin.natAdd l j := castAdd_lt_natAdd l' j
    have := hc.monotone (le_of_lt hlt)
    rw [Fin.le_def] at this
    omega
  -- a `1` in the last `H`-column, and the row of the copy that carries it
  obtain ⟨i0, hi0⟩ := hH.2 l'
  have hri0_new : n ≤ (r (Fin.castAdd p i0)).val := by
    by_contra hrow
    push Not at hrow
    have h1 : blockDiag X (blowup Z n) (r (Fin.castAdd p i0)) (c (Fin.castAdd q l')) = true := by
      rw [hentry (Fin.castAdd p i0) (Fin.castAdd q l'), blockDiag_castAdd_castAdd, hi0]
    rw [blockDiag_apply_old_new X (blowup Z n) hrow hlast_new] at h1
    exact Bool.false_ne_true h1
  -- group index of the `Z`-columns
  set γ : Fin q → ℕ := fun j => ((c (Fin.natAdd l j)).val - n) / (p * n) with hγ
  set γH : ℕ := ((c (Fin.castAdd q l')).val - n) / (p * n) with hγH
  have hγlt : ∀ j, γ j < q := fun j => div_lt_q (n := n) hn hp hq
  have hγHlt : γH < q := div_lt_q (n := n) hn hp hq
  by_cases hinj : Function.Injective γ
  · -- the `q` `Z`-columns hit all `q` groups, in particular the group of the last `H`-column
    have himg : (Finset.univ.image γ).card = q := by
      rw [Finset.card_image_of_injOn (fun a _ b _ h => hinj h), Finset.card_univ, Fintype.card_fin]
    have hEq : Finset.univ.image γ = Finset.range q := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (hγlt i)
      · rw [himg, Finset.card_range]
    have hmem : γH ∈ Finset.univ.image γ := by
      rw [hEq]
      exact Finset.mem_range.mpr hγHlt
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    have hcol := congrFun (col_eq_of_group_eq (Z := Z) (X := X) (hZcols_new j) hlast_new hj)
      (r (Fin.castAdd p i0))
    have h1 : blockDiag X (blowup Z n) (r (Fin.castAdd p i0)) (c (Fin.natAdd l j)) = false := by
      rw [hentry (Fin.castAdd p i0) (Fin.natAdd l j), blockDiag_castAdd_natAdd]
    have h2 : blockDiag X (blowup Z n) (r (Fin.castAdd p i0)) (c (Fin.castAdd q l')) = true := by
      rw [hentry (Fin.castAdd p i0) (Fin.castAdd q l'), blockDiag_castAdd_castAdd, hi0]
    rw [h1, h2] at hcol
    exact Bool.false_ne_true hcol
  · -- two `Z`-columns lie in the same group
    obtain ⟨j, j', hgrp, hjj'⟩ := Function.not_injective_iff.mp hinj
    have hZj : (fun i => Z i j) ≠ fun i => Z i j' := fun h => hjj' (hZ h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hZj
    have hcol := congrFun (col_eq_of_group_eq (Z := Z) (X := X) (hZcols_new j) (hZcols_new j')
      hgrp) (r (Fin.natAdd k i))
    have h1 : blockDiag X (blowup Z n) (r (Fin.natAdd k i)) (c (Fin.natAdd l j)) = Z i j := by
      rw [hentry (Fin.natAdd k i) (Fin.natAdd l j), blockDiag_natAdd_natAdd]
    have h2 : blockDiag X (blowup Z n) (r (Fin.natAdd k i)) (c (Fin.natAdd l j')) = Z i j' := by
      rw [hentry (Fin.natAdd k i) (Fin.natAdd l j'), blockDiag_natAdd_natAdd]
    rw [h1, h2] at hcol
    exact hi hcol

/-- **Step 1, rows from columns.**  If all `H`-columns of the copy are old, then all `H`-rows
are. -/
theorem step1_rows_old_of_cols_old (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H)
    (hk : 0 < k) (X : BMat n n) {r : Fin (k + p) → Fin (n + p * q * n)}
    {c : Fin (l + q) → Fin (n + p * q * n)}
    (hr : StrictMono r)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j)
    (hcols : ∀ j : Fin l, (c (Fin.castAdd q j)).val < n) :
    ∀ i : Fin k, (r (Fin.castAdd p i)).val < n := by
  classical
  set k' : Fin k := ⟨k - 1, by omega⟩ with hk'def
  intro i
  by_contra hnew
  push Not at hnew
  have hlast_new : n ≤ (r (Fin.castAdd p k')).val := by
    have hle : Fin.castAdd p i ≤ Fin.castAdd p k' := by
      rw [castAdd_le_castAdd_iff]
      exact Fin.le_def.mpr (by simp only [hk'def, Fin.val_mk]; omega)
    have hmono := hr.monotone hle
    rw [Fin.le_def] at hmono
    omega
  obtain ⟨j0, hj0⟩ := hH.1 k'
  have h1 : blockDiag X (blowup Z n) (r (Fin.castAdd p k')) (c (Fin.castAdd q j0)) = true := by
    rw [hentry (Fin.castAdd p k') (Fin.castAdd q j0), blockDiag_castAdd_castAdd, hj0]
  rw [blockDiag_apply_new_old X (blowup Z n) hlast_new (hcols j0)] at h1
  exact Bool.false_ne_true h1

/-! ## Step 1, assembled -/

/-- **Step 1.**  The `H`-rows and `H`-columns of a copy of `blockDiag H Z` in
`blockDiag X (blowup Z n)` are old. -/
theorem step1_old (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H) (hk : 0 < k)
    (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j)
    (X : BMat n n) {r : Fin (k + p) → Fin (n + p * q * n)}
    {c : Fin (l + q) → Fin (n + p * q * n)}
    (hr : StrictMono r) (hc : StrictMono c)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j) :
    (∀ i : Fin k, (r (Fin.castAdd p i)).val < n) ∧
      (∀ j : Fin l, (c (Fin.castAdd q j)).val < n) := by
  rcases hZ with hZ | hZ
  · exact ⟨step1_rows_old H Z hH hk hp hq hZ X hr hentry,
      step1_cols_old_of_rows_old H Z hH hk X hc hentry
        (step1_rows_old H Z hH hk hp hq hZ X hr hentry)⟩
  · exact ⟨step1_rows_old_of_cols_old H Z hH hk X hr hentry
        (step1_cols_old H Z hH hk hp hq hZ X hc hentry),
      step1_cols_old H Z hH hk hp hq hZ X hc hentry⟩

/-- **Step 1, restriction.**  The `H`-part of a copy whose `H`-rows and `H`-columns are old is a
copy of `H` in `X`. -/
theorem restrict_isCopy (H : BMat k l) (Z : BMat p q) (X : BMat n n)
    {r : Fin (k + p) → Fin (n + p * q * n)} {c : Fin (l + q) → Fin (n + p * q * n)}
    (hr : StrictMono r) (hc : StrictMono c)
    (hentry : ∀ i j, blockDiag X (blowup Z n) (r i) (c j) = blockDiag H Z i j)
    (hrows : ∀ i : Fin k, (r (Fin.castAdd p i)).val < n)
    (hcols : ∀ j : Fin l, (c (Fin.castAdd q j)).val < n) :
    IsCopy H X (fun i => ⟨(r (Fin.castAdd p i)).val, hrows i⟩)
      (fun j => ⟨(c (Fin.castAdd q j)).val, hcols j⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h1 : Fin.castAdd p i < Fin.castAdd p j := castAdd_lt_castAdd_iff.mpr hij
    exact Fin.lt_def.mp (hr h1)
  · intro i j hij
    have h1 : Fin.castAdd q i < Fin.castAdd q j := castAdd_lt_castAdd_iff.mpr hij
    exact Fin.lt_def.mp (hc h1)
  · intro i j
    have h := hentry (Fin.castAdd p i) (Fin.castAdd q j)
    rw [blockDiag_castAdd_castAdd] at h
    rw [← h]
    exact (blockDiag_apply_old_old X (blowup Z n) (hrows i) (hcols j)).symm

/-- **Step 1, corollary.**  If `X` is `H`-free, then `blockDiag X (blowup Z n)` is
`blockDiag H Z`-free. -/
theorem free_blockDiag (H : BMat k l) (Z : BMat p q) (hH : NoZeroLine H) (hk : 0 < k)
    (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j)
    (X : BMat n n) (hX : Free H X) :
    Free (blockDiag H Z) (blockDiag X (blowup Z n)) := by
  rintro ⟨r, c, hr, hc, hentry⟩
  obtain ⟨hrows, hcols⟩ := step1_old H Z hH hk hp hq hZ X hr hc hentry
  exact hX ⟨_, _, restrict_isCopy H Z X hr hc hentry hrows hcols⟩

/-- Split a double sum over `Fin (k+p) × Fin (l+q)` into the four blocks. -/
theorem sum_four_blocks {k l p q : ℕ} (F : Fin (k + p) → Fin (l + q) → ℕ) :
    (∑ i, ∑ j, F i j) =
      (∑ i : Fin k, ∑ j : Fin l, F (Fin.castAdd p i) (Fin.castAdd q j))
      + (∑ i : Fin k, ∑ j : Fin q, F (Fin.castAdd p i) (Fin.natAdd l j))
      + (∑ i : Fin p, ∑ j : Fin l, F (Fin.natAdd k i) (Fin.castAdd q j))
      + (∑ i : Fin p, ∑ j : Fin q, F (Fin.natAdd k i) (Fin.natAdd l j)) := by
  have step : ∀ i : Fin (k + p),
      (∑ j : Fin (l + q), F i j) =
        (∑ j : Fin l, F i (Fin.castAdd q j)) + (∑ j : Fin q, F i (Fin.natAdd l j)) :=
    fun i => Fin.sum_univ_add _
  calc (∑ i, ∑ j, F i j)
      = ∑ i, ((∑ j : Fin l, F i (Fin.castAdd q j)) + (∑ j : Fin q, F i (Fin.natAdd l j))) :=
        Finset.sum_congr rfl fun i _ => step i
    _ = (∑ i, ∑ j : Fin l, F i (Fin.castAdd q j)) + (∑ i, ∑ j : Fin q, F i (Fin.natAdd l j)) :=
        Finset.sum_add_distrib
    _ = ((∑ i : Fin k, ∑ j : Fin l, F (Fin.castAdd p i) (Fin.castAdd q j))
          + (∑ i : Fin p, ∑ j : Fin l, F (Fin.natAdd k i) (Fin.castAdd q j)))
        + ((∑ i : Fin k, ∑ j : Fin q, F (Fin.castAdd p i) (Fin.natAdd l j))
          + (∑ i : Fin p, ∑ j : Fin q, F (Fin.natAdd k i) (Fin.natAdd l j))) := by
        rw [Fin.sum_univ_add (f := fun i => ∑ j : Fin l, F i (Fin.castAdd q j)),
            Fin.sum_univ_add (f := fun i => ∑ j : Fin q, F i (Fin.natAdd l j))]
    _ = _ := by abel

theorem hamming_blockDiag {k l p q : ℕ} (H₁ H₂ : BMat k l) (W₁ W₂ : BMat p q) :
    hamming (blockDiag H₁ W₁) (blockDiag H₂ W₂) = hamming H₁ H₂ + hamming W₁ W₂ := by
  rw [hamming_eq_sum (blockDiag H₁ W₁) (blockDiag H₂ W₂), Fintype.sum_prod_type,
    sum_four_blocks (fun i j => if blockDiag H₁ W₁ i j = blockDiag H₂ W₂ i j then 0 else 1),
    hamming_eq_sum, hamming_eq_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [blockDiag]

theorem hamming_blockDiag_same {k l p q : ℕ} (H₁ H₂ : BMat k l) (W : BMat p q) :
    hamming (blockDiag H₁ W) (blockDiag H₂ W) = hamming H₁ H₂ := by
  rw [hamming_blockDiag, hamming_self, add_zero]




open Classical

variable {p q n : ℕ}

/-! ## Fibres of `Fin p → Fin N` at one coordinate -/

/-- Functions `Fin p → Fin N` with a prescribed value at `j` are the functions on the other
coordinates. -/
def fibreEquiv (N : ℕ) (j : Fin p) (w : Fin N) :
    {γ : Fin p → Fin N // γ j = w} ≃ ({i : Fin p // i ≠ j} → Fin N) where
  toFun γ := fun i => γ.1 i.1
  invFun g := ⟨fun i => if h : i = j then w else g ⟨i, h⟩, by simp⟩
  left_inv γ := by
    refine Subtype.ext (funext fun i => ?_)
    by_cases h : i = j
    · subst h
      simp [γ.2]
    · simp [h]
  right_inv g := by
    funext i
    simp [i.2]

/-- The complement of a point in `Fin p` has `p - 1` elements. -/
lemma card_ne_fin (j : Fin p) : Fintype.card {i : Fin p // i ≠ j} = p - 1 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun i : Fin p => i ≠ j)) = Finset.univ.erase j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- The number of functions `Fin p → Fin N` taking the value `w` at `j`. -/
lemma card_fibre_eval (N : ℕ) (j : Fin p) (w : Fin N) :
    (Finset.univ.filter (fun γ : Fin p → Fin N => γ j = w)).card = N ^ (p - 1) := by
  rw [← Fintype.card_subtype (fun γ : Fin p → Fin N => γ j = w)]
  rw [Fintype.card_congr (fibreEquiv N j w), Fintype.card_fun, card_ne_fin, Fintype.card_fin]

/-- Summing a function of one coordinate over all functions: each value occurs `N^(p-1)` times. -/
lemma sum_fibre_eval (N : ℕ) (j : Fin p) (f : Fin N → ℕ) :
    (∑ γ : Fin p → Fin N, f (γ j)) = N ^ (p - 1) * (∑ w : Fin N, f w) := by
  have h1 : (∑ γ : Fin p → Fin N, f (γ j))
      = ∑ x : Fin N × ({i : Fin p // i ≠ j} → Fin N), f x.1 := by
    refine Fintype.sum_equiv (Equiv.funSplitAt j (Fin N)) (fun γ => f (γ j))
      (fun x => f x.1) ?_
    intro γ
    simp [Equiv.funSplitAt_apply]
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ w : Fin N,
      (∑ _g : ({i : Fin p // i ≠ j} → Fin N), f w) = N ^ (p - 1) * f w := by
    intro w
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, card_ne_fin, Fintype.card_fin,
      smul_eq_mul]
  rw [Finset.sum_congr rfl (fun w _ => h2 w), ← Finset.mul_sum]

/-- **The pick fibre, rows.**  For a fixed offset `w` in row group `j`, exactly
`(q*n)^(p-1)` of the `(q*n)^p` row picks take the value `w` there. -/
lemma sum_rowpick_eval (j : Fin p) (f : Fin (q * n) → ℕ) :
    (∑ ρ : Fin p → Fin (q * n), f (ρ j)) = (q * n) ^ (p - 1) * (∑ v, f v) :=
  sum_fibre_eval (q * n) j f

/-- **The pick fibre, columns.** -/
lemma sum_colpick_eval (j : Fin q) (f : Fin (p * n) → ℕ) :
    (∑ γ : Fin q → Fin (p * n), f (γ j)) = (p * n) ^ (q - 1) * (∑ w, f w) :=
  sum_fibre_eval (p * n) j f

/-! ## Reindexing the new coordinates by group and offset -/

/-- `pickRow` and the API file's `rowRep` are the same function. -/
lemma pickRow_eq_rowRep (i : Fin p) (v : Fin (q * n)) : pickRow i v = rowRep i v := Fin.ext rfl

/-- `pickCol` and the API file's `colRep` are the same function. -/
lemma pickCol_eq_colRep (j : Fin q) (w : Fin (p * n)) : pickCol j w = colRep j w := Fin.ext rfl

/-- Summing over the new rows is summing over the row groups and the offsets in each group. -/
lemma sum_new_row {M : Type*} [AddCommMonoid M] (hqn : 0 < q * n)
    (f : Fin (p * q * n) → M) :
    (∑ r : Fin (p * q * n), f r) = ∑ i : Fin p, ∑ v : Fin (q * n), f (pickRow i v) := by
  have hsurj : Function.Surjective (fun x : Fin p × Fin (q * n) => pickRow x.1 x.2) := by
    intro b
    obtain ⟨t, ht⟩ := rowRep_surjective (p := p) (n := n) hqn
      ⟨b.val / (q * n), blowup_row_lt (n := n) b⟩ (i := b) rfl
    exact ⟨(⟨b.val / (q * n), blowup_row_lt (n := n) b⟩, t), by
      simpa [pickRow_eq_rowRep] using ht⟩
  rw [← Fintype.sum_prod_type (f := fun x : Fin p × Fin (q * n) => f (pickRow x.1 x.2))]
  exact (Fintype.sum_bijective (fun x : Fin p × Fin (q * n) => pickRow x.1 x.2)
    ⟨pickRow_injective, hsurj⟩ (fun x => f (pickRow x.1 x.2)) f (fun x => rfl)).symm

/-- Summing over the new columns is summing over the column groups and the offsets in each
group. -/
lemma sum_new_col {M : Type*} [AddCommMonoid M] (hpn : 0 < p * n)
    (f : Fin (p * q * n) → M) :
    (∑ c : Fin (p * q * n), f c) = ∑ j : Fin q, ∑ w : Fin (p * n), f (pickCol j w) := by
  have hsurj : Function.Surjective (fun x : Fin q × Fin (p * n) => pickCol x.1 x.2) := by
    intro b
    obtain ⟨t, ht⟩ := colRep_surjective (q := q) (n := n) hpn
      ⟨b.val / (p * n), blowup_col_lt (n := n) b⟩ (i := b) rfl
    exact ⟨(⟨b.val / (p * n), blowup_col_lt (n := n) b⟩, t), by
      simpa [pickCol_eq_colRep] using ht⟩
  rw [← Fintype.sum_prod_type (f := fun x : Fin q × Fin (p * n) => f (pickCol x.1 x.2))]
  exact (Fintype.sum_bijective (fun x : Fin q × Fin (p * n) => pickCol x.1 x.2)
    ⟨pickCol_injective, hsurj⟩ (fun x => f (pickCol x.1 x.2)) f (fun x => rfl)).symm




open Classical

variable {k l p q n : ℕ}

/-! ## Reindexing the error blocks -/

/-- `E₁ᵃ`, the old-row/new-column block, reindexed by column group and offset. -/
lemma E1a_eq (B : BMat (n + p * q * n) (n + p * q * n)) (hpn : 0 < p * n) :
    E1a B = ∑ r : Fin n, ∑ j : Fin q, ∑ w : Fin (p * n),
      (if B (oldRow n p q r) (newIdx n p q (pickCol j w)) = true then 1 else 0) := by
  unfold E1a
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact sum_new_col (n := n) (p := p) (q := q) hpn
    (fun c => if B (oldRow n p q r) (newIdx n p q c) = true then 1 else 0)

/-- `E₁ᵇ`, the new-row/old-column block, reindexed by row group and offset. -/
lemma E1b_eq (B : BMat (n + p * q * n) (n + p * q * n)) (hqn : 0 < q * n) :
    E1b B = ∑ i : Fin p, ∑ v : Fin (q * n), ∑ c : Fin n,
      (if B (newIdx n p q (pickRow i v)) (oldRow n p q c) = true then 1 else 0) := by
  unfold E1b
  rw [sum_new_row (n := n) (p := p) (q := q) hqn]

/-- `E₂`, the new-new block, reindexed by group and offset on both sides. -/
lemma E2_eq (Z : BMat p q) (B : BMat (n + p * q * n) (n + p * q * n))
    (hqn : 0 < q * n) (hpn : 0 < p * n) :
    E2 Z B = ∑ i : Fin p, ∑ v : Fin (q * n), ∑ j : Fin q, ∑ w : Fin (p * n),
      (if Z i j ≠ B (newIdx n p q (pickRow i v)) (newIdx n p q (pickCol j w)) then 1 else 0) := by
  unfold E2
  rw [sum_new_row (n := n) (p := p) (q := q) hqn]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [sum_new_col (n := n) (p := p) (q := q) hpn]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [blowup_pick]

/-! ## `B°` and the `E₀ + W` bound -/

/-- `hamming` as an iterated sum of indicators. -/
lemma hamming_double_sum (A B : BMat n n) :
    hamming A B = ∑ i : Fin n, ∑ j : Fin n, (if A i j ≠ B i j then 1 else 0) := by
  rw [hamming, card_filter_eq_sum, Fintype.sum_prod_type]

/-- The number of bad old rows of a pick. -/
noncomputable def badRowCount (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) : ℕ :=
  ∑ r : Fin n, if badRow B x r then 1 else 0

/-- The number of bad old columns of a pick. -/
noncomputable def badColCount (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) : ℕ :=
  ∑ c : Fin n, if badCol B x c then 1 else 0

/-- `W = n · (number of bad lines)`: the number of old-old entries that `B°` may destroy. -/
noncomputable def lineCost (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) : ℕ :=
  (∑ r : Fin n, if badRow B x r then n else 0)
    + (∑ c : Fin n, if badCol B x c then n else 0)

/-- Zeroing a bad line changes at most `n` entries in it. -/
lemma indicator_Bcirc_le (A : BMat n n) (B : BMat (n + p * q * n) (n + p * q * n))
    (x : Pick p q n) (r c : Fin n) :
    (if A r c ≠ Bcirc B x r c then 1 else 0) ≤
      (if A r c ≠ B (oldRow n p q r) (oldRow n p q c) then 1 else 0)
        + (if badRow B x r then 1 else 0) + (if badCol B x c then 1 else 0) := by
  by_cases hb : badRow B x r ∨ badCol B x c
  · have h1 : 1 ≤ (if badRow B x r then 1 else 0) + (if badCol B x c then 1 else 0) := by
      rcases hb with hr | hc
      · simp [hr]
      · simp [hc]
    have h2 : (if A r c ≠ Bcirc B x r c then 1 else 0) ≤ 1 := by split <;> simp
    omega
  · have hbc : Bcirc B x r c = B (oldRow n p q r) (oldRow n p q c) := by
      unfold Bcirc
      rw [if_neg hb]
    have hr : ¬ badRow B x r := fun h => hb (Or.inl h)
    have hc : ¬ badCol B x c := fun h => hb (Or.inr h)
    rw [hbc]
    simp [hr, hc]

/-- **`D ≤ E₀ + W`.**  Replacing every bad row and bad column of the old-old block of `B` by
zeros costs at most `E₀` changed entries plus `n` per bad line. -/
lemma hamming_Bcirc_le (A : BMat n n) (B : BMat (n + p * q * n) (n + p * q * n))
    (x : Pick p q n) :
    hamming A (Bcirc B x) ≤ Eold A B + lineCost B x := by
  rw [hamming_double_sum]
  have hstep : (∑ r : Fin n, ∑ c : Fin n, (if A r c ≠ Bcirc B x r c then 1 else 0))
      ≤ ∑ r : Fin n, ∑ c : Fin n,
          ((if A r c ≠ B (oldRow n p q r) (oldRow n p q c) then 1 else 0)
            + (if badRow B x r then 1 else 0) + (if badCol B x c then 1 else 0)) :=
    Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun c _ => indicator_Bcirc_le A B x r c))
  refine le_trans hstep ?_
  have hsplit : ∀ r : Fin n,
      (∑ c : Fin n, ((if A r c ≠ B (oldRow n p q r) (oldRow n p q c) then 1 else 0)
            + (if badRow B x r then 1 else 0) + (if badCol B x c then 1 else 0)))
        = (∑ c : Fin n, (if A r c ≠ B (oldRow n p q r) (oldRow n p q c) then 1 else 0))
          + (if badRow B x r then n else 0)
          + (∑ c : Fin n, (if badCol B x c then 1 else 0)) := by
    intro r
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hconst : (∑ _c : Fin n, (if badRow B x r then 1 else 0)) = (if badRow B x r then n else 0) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      split <;> simp
    rw [hconst]
  rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hcol : (∑ _r : Fin n, ∑ c : Fin n, (if badCol B x c then 1 else 0))
      = ∑ c : Fin n, (if badCol B x c then n else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    split <;> simp
  rw [hcol]
  unfold Eold lineCost
  omega




open Classical

section Picks

variable {p q n : ℕ}

/-- A sum over all picks of a function of the `i`-th row pick. -/
lemma sum_picks_row (f : Fin (q * n) → ℕ) (i : Fin p) :
    (∑ x : Pick p q n, f (x.1 i)) = (p * n) ^ q * ((q * n) ^ (p - 1) * ∑ v, f v) := by
  have h1 : (∑ x : Pick p q n, f (x.1 i))
      = ∑ ρ : Fin p → Fin (q * n), ∑ _γ : Fin q → Fin (p * n), f (ρ i) := by
    rw [Fintype.sum_prod_type]
  rw [h1]
  have h2 : ∀ ρ : Fin p → Fin (q * n),
      (∑ _γ : Fin q → Fin (p * n), f (ρ i)) = (p * n) ^ q * f (ρ i) := by
    intro ρ
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl (fun ρ _ => h2 ρ), ← Finset.mul_sum, sum_rowpick_eval]

/-- A sum over all picks of a function of the `j`-th column pick. -/
lemma sum_picks_col (f : Fin (p * n) → ℕ) (j : Fin q) :
    (∑ x : Pick p q n, f (x.2 j)) = (q * n) ^ p * ((p * n) ^ (q - 1) * ∑ w, f w) := by
  have h1 : (∑ x : Pick p q n, f (x.2 j))
      = ∑ _ρ : Fin p → Fin (q * n), ∑ γ : Fin q → Fin (p * n), f (γ j) := by
    rw [Fintype.sum_prod_type]
  rw [h1]
  have h2 : ∀ _ρ : Fin p → Fin (q * n),
      (∑ γ : Fin q → Fin (p * n), f (γ j)) = (p * n) ^ (q - 1) * ∑ w, f w :=
    fun _ => sum_colpick_eval j f
  rw [Finset.sum_congr rfl (fun ρ _ => h2 ρ), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, smul_eq_mul]
  norm_num

end Picks

section BadRows

variable {p q n : ℕ}

/-- **Bad rows.**  Each bad old row accounts for a `1` of `B` in the old-row/new-column block. -/
lemma sum_badRowCount_le (B : BMat (n + p * q * n) (n + p * q * n))
    (hqn : 0 < q * n) (hpn : 0 < p * n) (hq : 0 < q) :
    (p * n) * (∑ x : Pick p q n, badRowCount B x)
      ≤ ((q * n) ^ p * (p * n) ^ q) * E1a B := by
  classical
  set c : Fin n → Fin q → ℕ := fun r j => ∑ w : Fin (p * n),
      (if B (oldRow n p q r) (newIdx n p q (pickCol j w)) = true then 1 else 0) with hc
  have hstep1 : (∑ x : Pick p q n, badRowCount B x)
      ≤ ∑ x : Pick p q n, ∑ r : Fin n, ∑ j : Fin q,
          (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0) := by
    refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun r _ => ?_))
    by_cases h : badRow B x r
    · rw [if_pos h]
      obtain ⟨j0, hj0⟩ := h
      have hsingle : (if B (oldRow n p q r) (pickColN x j0) = true then (1 : ℕ) else 0)
          ≤ ∑ j : Fin q,
              (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0) :=
        Finset.single_le_sum (f := fun j : Fin q =>
          (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      rw [if_pos hj0] at hsingle
      exact hsingle
    · rw [if_neg h]
      exact Nat.zero_le _
  refine le_trans (Nat.mul_le_mul_left (p * n) hstep1) ?_
  have hswap : (∑ x : Pick p q n, ∑ r : Fin n, ∑ j : Fin q,
        (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0))
      = ∑ r : Fin n, ∑ j : Fin q, ∑ x : Pick p q n,
        (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)
  rw [hswap]
  have hval : ∀ (r : Fin n) (j : Fin q),
      (∑ x : Pick p q n, (if B (oldRow n p q r) (pickColN x j) = true then 1 else 0))
        = (q * n) ^ p * ((p * n) ^ (q - 1) * c r j) := by
    intro r j
    rw [hc]
    exact sum_picks_col (fun w => if B (oldRow n p q r) (newIdx n p q (pickCol j w)) = true
      then 1 else 0) j
  rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => hval r j))]
  have hpull : (∑ r : Fin n, ∑ j : Fin q, (q * n) ^ p * ((p * n) ^ (q - 1) * c r j))
      = (q * n) ^ p * ((p * n) ^ (q - 1) * ∑ r : Fin n, ∑ j : Fin q, c r j) := by
    have step1 : ∀ r : Fin n,
        (∑ j : Fin q, (q * n) ^ p * ((p * n) ^ (q - 1) * c r j))
          = (q * n) ^ p * ((p * n) ^ (q - 1) * ∑ j : Fin q, c r j) := by
      intro r
      rw [← Finset.mul_sum]
      exact congrArg (fun t => (q * n) ^ p * t) (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun r _ => step1 r), ← Finset.mul_sum]
    exact congrArg (fun t => (q * n) ^ p * t) (Finset.mul_sum _ _ _).symm
  rw [hpull]
  have hE : (∑ r : Fin n, ∑ j : Fin q, c r j) = E1a B := by
    rw [hc]
    exact (E1a_eq B hpn).symm
  rw [hE]
  have hpow : (p * n) * (p * n) ^ (q - 1) = (p * n) ^ q := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hq]
  have heq : (p * n) * ((q * n) ^ p * ((p * n) ^ (q - 1) * E1a B))
      = ((q * n) ^ p * (p * n) ^ q) * E1a B := by
    rw [← hpow]; ring
  rw [heq]

/-- **Bad columns.**  Each bad old column accounts for a `1` of `B` in the new-row/old-column
block. -/
lemma sum_badColCount_le (B : BMat (n + p * q * n) (n + p * q * n))
    (hqn : 0 < q * n) (hpn : 0 < p * n) (hp : 0 < p) :
    (q * n) * (∑ x : Pick p q n, badColCount B x)
      ≤ ((q * n) ^ p * (p * n) ^ q) * E1b B := by
  classical
  set c : Fin n → Fin p → ℕ := fun col i => ∑ v : Fin (q * n),
      (if B (newIdx n p q (pickRow i v)) (oldRow n p q col) = true then 1 else 0) with hc
  have hstep1 : (∑ x : Pick p q n, badColCount B x)
      ≤ ∑ x : Pick p q n, ∑ col : Fin n, ∑ i : Fin p,
          (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0) := by
    refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun col _ => ?_))
    by_cases h : badCol B x col
    · rw [if_pos h]
      obtain ⟨i0, hi0⟩ := h
      have hsingle : (if B (pickRowN x i0) (oldRow n p q col) = true then (1 : ℕ) else 0)
          ≤ ∑ i : Fin p,
              (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0) :=
        Finset.single_le_sum (f := fun i : Fin p =>
          (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
      rw [if_pos hi0] at hsingle
      exact hsingle
    · rw [if_neg h]
      exact Nat.zero_le _
  refine le_trans (Nat.mul_le_mul_left (q * n) hstep1) ?_
  have hswap : (∑ x : Pick p q n, ∑ col : Fin n, ∑ i : Fin p,
        (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0))
      = ∑ col : Fin n, ∑ i : Fin p, ∑ x : Pick p q n,
        (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun col _ => Finset.sum_comm)
  rw [hswap]
  have hval : ∀ (col : Fin n) (i : Fin p),
      (∑ x : Pick p q n, (if B (pickRowN x i) (oldRow n p q col) = true then 1 else 0))
        = (p * n) ^ q * ((q * n) ^ (p - 1) * c col i) := by
    intro col i
    rw [hc]
    exact sum_picks_row (fun v => if B (newIdx n p q (pickRow i v)) (oldRow n p q col) = true
      then 1 else 0) i
  rw [Finset.sum_congr rfl (fun col _ => Finset.sum_congr rfl (fun i _ => hval col i))]
  have hpull : (∑ col : Fin n, ∑ i : Fin p, (p * n) ^ q * ((q * n) ^ (p - 1) * c col i))
      = (p * n) ^ q * ((q * n) ^ (p - 1) * ∑ col : Fin n, ∑ i : Fin p, c col i) := by
    have step1 : ∀ col : Fin n,
        (∑ i : Fin p, (p * n) ^ q * ((q * n) ^ (p - 1) * c col i))
          = (p * n) ^ q * ((q * n) ^ (p - 1) * ∑ i : Fin p, c col i) := by
      intro col
      rw [← Finset.mul_sum]
      exact congrArg (fun t => (p * n) ^ q * t) (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun col _ => step1 col), ← Finset.mul_sum]
    exact congrArg (fun t => (p * n) ^ q * t) (Finset.mul_sum _ _ _).symm
  rw [hpull]
  have hE : (∑ col : Fin n, ∑ i : Fin p, c col i) = E1b B := by
    rw [hc]
    rw [E1b_eq B hqn]
    have l1 : (∑ col : Fin n, ∑ i : Fin p, ∑ v : Fin (q * n),
          (if B (newIdx n p q (pickRow i v)) (oldRow n p q col) = true then 1 else 0))
        = ∑ i : Fin p, ∑ col : Fin n, ∑ v : Fin (q * n),
          (if B (newIdx n p q (pickRow i v)) (oldRow n p q col) = true then 1 else 0) :=
      Finset.sum_comm
    rw [l1]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  rw [hE]
  have hpow : (q * n) * (q * n) ^ (p - 1) = (q * n) ^ p := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hp]
  have heq : (q * n) * ((p * n) ^ q * ((q * n) ^ (p - 1) * E1b B))
      = ((q * n) ^ p * (p * n) ^ q) * E1b B := by
    rw [← hpow]; ring
  rw [heq]

end BadRows

section GoodPicks

variable {p q n : ℕ}

/-- `E₂` with the offsets summed first. -/
lemma E2_eq' (Z : BMat p q) (B : BMat (n + p * q * n) (n + p * q * n))
    (hqn : 0 < q * n) (hpn : 0 < p * n) :
    E2 Z B = ∑ i : Fin p, ∑ j : Fin q, ∑ v : Fin (q * n), ∑ w : Fin (p * n),
      (if Z i j ≠ B (newIdx n p q (pickRow i v)) (newIdx n p q (pickCol j w)) then 1 else 0) := by
  rw [E2_eq Z B hqn hpn]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Finset.sum_comm

/-- **The good picks.**  A fixed new-new entry is picked by a proportion `1/((pn)(qn))` of all
picks, so the non-good picks are at most `E₂` times the number of picks divided by `(pn)(qn)`. -/
lemma card_notGood_le (Z : BMat p q) (B : BMat (n + p * q * n) (n + p * q * n))
    (hqn : 0 < q * n) (hpn : 0 < p * n) (hp : 0 < p) (hq : 0 < q) :
    (p * n) * (q * n) * (Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card
      ≤ ((q * n) ^ p * (p * n) ^ q) * E2 Z B := by
  classical
  set d : Fin p → Fin q → ℕ := fun i j => ∑ v : Fin (q * n), ∑ w : Fin (p * n),
      (if Z i j ≠ B (newIdx n p q (pickRow i v)) (newIdx n p q (pickCol j w)) then 1 else 0)
    with hd
  have hcard : (Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card
      = ∑ x : Pick p q n, (if ¬ Good Z B x then 1 else 0) := card_filter_eq_sum _
  rw [hcard]
  have hstep : (∑ x : Pick p q n, (if ¬ Good Z B x then 1 else 0))
      ≤ ∑ x : Pick p q n, ∑ i : Fin p, ∑ j : Fin q,
          (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    by_cases h : Good Z B x
    · rw [if_neg (not_not_intro h)]
      exact Nat.zero_le _
    · rw [if_pos h]
      have hex : ∃ i j, Z i j ≠ B (pickRowN x i) (pickColN x j) := by
        by_contra hc
        simp only [not_exists, not_ne_iff] at hc
        exact h (fun i j => (hc i j).symm)
      obtain ⟨i0, j0, hij⟩ := hex
      have hsingle : (if Z i0 j0 ≠ B (pickRowN x i0) (pickColN x j0) then (1 : ℕ) else 0)
          ≤ ∑ j : Fin q, (if Z i0 j ≠ B (pickRowN x i0) (pickColN x j) then 1 else 0) :=
        Finset.single_le_sum (f := fun j : Fin q =>
          (if Z i0 j ≠ B (pickRowN x i0) (pickColN x j) then 1 else 0))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      rw [if_pos hij] at hsingle
      refine le_trans hsingle ?_
      exact Finset.single_le_sum (f := fun i : Fin p =>
          ∑ j : Fin q, (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
  refine le_trans (Nat.mul_le_mul_left ((p * n) * (q * n)) hstep) ?_
  have hswap : (∑ x : Pick p q n, ∑ i : Fin p, ∑ j : Fin q,
        (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0))
      = ∑ i : Fin p, ∑ j : Fin q, ∑ x : Pick p q n,
        (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  rw [hswap]
  have hval : ∀ (i : Fin p) (j : Fin q),
      (∑ x : Pick p q n, (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0))
        = (p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * d i j) := by
    intro i j
    rw [hd]
    have e1 : (∑ x : Pick p q n, (if Z i j ≠ B (pickRowN x i) (pickColN x j) then 1 else 0))
        = ∑ ρ : Fin p → Fin (q * n), ∑ γ : Fin q → Fin (p * n),
            (if Z i j ≠ B (newIdx n p q (pickRow i (ρ i)))
              (newIdx n p q (pickCol j (γ j))) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
    rw [e1]
    have e2 : ∀ ρ : Fin p → Fin (q * n),
        (∑ γ : Fin q → Fin (p * n),
            (if Z i j ≠ B (newIdx n p q (pickRow i (ρ i)))
              (newIdx n p q (pickCol j (γ j))) then 1 else 0))
          = (p * n) ^ (q - 1) * ∑ w : Fin (p * n),
            (if Z i j ≠ B (newIdx n p q (pickRow i (ρ i)))
              (newIdx n p q (pickCol j w)) then 1 else 0) :=
      fun ρ => sum_colpick_eval (p := p) (q := q) (n := n) j
        (fun w => if Z i j ≠ B (newIdx n p q (pickRow i (ρ i)))
          (newIdx n p q (pickCol j w)) then 1 else 0)
    rw [Finset.sum_congr rfl (fun ρ _ => e2 ρ), ← Finset.mul_sum]
    congr 1
    have e3 : (∑ ρ : Fin p → Fin (q * n), ∑ w : Fin (p * n),
          (if Z i j ≠ B (newIdx n p q (pickRow i (ρ i)))
            (newIdx n p q (pickCol j w)) then 1 else 0))
        = (q * n) ^ (p - 1) * ∑ v : Fin (q * n), ∑ w : Fin (p * n),
          (if Z i j ≠ B (newIdx n p q (pickRow i v))
            (newIdx n p q (pickCol j w)) then 1 else 0) :=
      sum_rowpick_eval (p := p) (q := q) (n := n) i
        (fun v => ∑ w : Fin (p * n),
          (if Z i j ≠ B (newIdx n p q (pickRow i v))
            (newIdx n p q (pickCol j w)) then 1 else 0))
    rw [e3]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval i j))]
  have hpull : (∑ i : Fin p, ∑ j : Fin q, (p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * d i j))
      = (p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * ∑ i : Fin p, ∑ j : Fin q, d i j) := by
    have step1 : ∀ i : Fin p,
        (∑ j : Fin q, (p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * d i j))
          = (p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * ∑ j : Fin q, d i j) := by
      intro i
      rw [← Finset.mul_sum]
      exact congrArg (fun t => (p * n) ^ (q - 1) * t) (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun i _ => step1 i), ← Finset.mul_sum]
    exact congrArg (fun t => (p * n) ^ (q - 1) * t) (Finset.mul_sum _ _ _).symm
  rw [hpull]
  have hE : (∑ i : Fin p, ∑ j : Fin q, d i j) = E2 Z B := by
    rw [hd, E2_eq' Z B hqn hpn]
  rw [hE]
  have hpow1 : (q * n) * (q * n) ^ (p - 1) = (q * n) ^ p := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hp]
  have hpow2 : (p * n) * (p * n) ^ (q - 1) = (p * n) ^ q := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hq]
  have heq : (p * n) * (q * n) * ((p * n) ^ (q - 1) * ((q * n) ^ (p - 1) * E2 Z B))
      = ((q * n) ^ p * (p * n) ^ q) * E2 Z B := by
    rw [← hpow1, ← hpow2]; ring
  rw [heq]

end GoodPicks




open Classical

section Lower

variable {k l p q n : ℕ}

/-- A bad line costs `n` entries, so `lineCost` is `n` times the bad line counts. -/
lemma lineCost_eq (B : BMat (n + p * q * n) (n + p * q * n)) (x : Pick p q n) :
    lineCost B x = n * badRowCount B x + n * badColCount B x := by
  unfold lineCost badRowCount badColCount
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by split <;> simp)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => by split <;> simp)

theorem editDist_le_hamming_of_free (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q) (hn : 0 < n)
    (A : BMat n n) (B : BMat (n + p * q * n) (n + p * q * n))
    (hB : Free (blockDiag H Z) B) :
    editDist H A ≤ hamming (blockDiag A (blowup Z n)) B := by
  classical
  have hqn : 0 < q * n := Nat.mul_pos hq hn
  have hpn : 0 < p * n := Nat.mul_pos hp hn
  -- `H` contains a `1`, hence `D ≤ n²`
  obtain ⟨i0, j0, hij0⟩ : ∃ i j, H i j = true :=
    ⟨⟨0, hk⟩, (hH.1 ⟨0, hk⟩).choose, (hH.1 ⟨0, hk⟩).choose_spec⟩
  set D := editDist H A with hDdef
  set E0 := Eold A B with hE0
  set E1 := E1a B + E1b B with hE1
  set E2v := E2 Z B with hE2
  set Np := (q * n) ^ p * (p * n) ^ q with hNp
  set S := (p * n) * (q * n) with hS
  have hDle : D ≤ n * n := by
    rw [hDdef]
    exact editDist_le_zero H A ⟨i0, j0, hij0⟩
  have hDS : D ≤ S := by
    have h1 : n * n ≤ (p * n) * (q * n) := by
      apply Nat.mul_le_mul
      · calc n = 1 * n := (one_mul n).symm
          _ ≤ p * n := Nat.mul_le_mul_right n hp
      · calc n = 1 * n := (one_mul n).symm
          _ ≤ q * n := Nat.mul_le_mul_right n hq
    omega
  have hSpos : 0 < S := Nat.mul_pos hpn hqn
  have hNpos : 0 < Np := by
    rw [hNp]
    exact Nat.mul_pos (pow_pos hqn p) (pow_pos hpn q)
  -- ## the pointwise inequality over the pick space
  have hpt : ∀ x : Pick p q n, (if Good Z B x then D else 0) ≤ E0 + lineCost B x := by
    intro x
    by_cases hx : Good Z B x
    · rw [if_pos hx]
      have hfree : Free H (Bcirc B x) := good_free H hH Z B hB x hx
      have h1 : D ≤ hamming A (Bcirc B x) := by
        rw [hDdef]
        exact editDist_le H A _ hfree
      have h2 : hamming A (Bcirc B x) ≤ E0 + lineCost B x := by
        rw [hE0]
        exact hamming_Bcirc_le A B x
      omega
    · rw [if_neg hx]
      exact Nat.zero_le _
  -- ## the sum over all picks
  have hLHS : (∑ x : Pick p q n, (if Good Z B x then D else 0))
      = (Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card * D := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul]
  have hcardPick : Fintype.card (Pick p q n) = Np := by
    rw [hNp]
    simp [Pick, Fintype.card_prod]
  have hRHS : (∑ x : Pick p q n, (E0 + lineCost B x))
      = Np * E0 + ∑ x : Pick p q n, lineCost B x := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardPick, smul_eq_mul]
  have hsum1 : (Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card * D
      ≤ Np * E0 + ∑ x : Pick p q n, lineCost B x := by
    rw [← hLHS, ← hRHS]
    exact Finset.sum_le_sum (fun x _ => hpt x)
  -- ## bounding the total line cost
  have hline : (∑ x : Pick p q n, lineCost B x) ≤ Np * (E1a B + E1b B) := by
    have hsplit : (∑ x : Pick p q n, lineCost B x)
        = n * (∑ x : Pick p q n, badRowCount B x)
          + n * (∑ x : Pick p q n, badColCount B x) := by
      rw [Finset.sum_congr rfl (fun x _ => lineCost_eq B x), Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    rw [hsplit]
    have hbr : n * (∑ x : Pick p q n, badRowCount B x) ≤ Np * E1a B := by
      have h := sum_badRowCount_le (p := p) (q := q) (n := n) B hqn hpn hq
      have hle : n * (∑ x : Pick p q n, badRowCount B x)
          ≤ (p * n) * (∑ x : Pick p q n, badRowCount B x) := by
        apply Nat.mul_le_mul_right
        calc n = 1 * n := (one_mul n).symm
          _ ≤ p * n := Nat.mul_le_mul_right n hp
      exact le_trans hle h
    have hbc : n * (∑ x : Pick p q n, badColCount B x) ≤ Np * E1b B := by
      have h := sum_badColCount_le (p := p) (q := q) (n := n) B hqn hpn hp
      have hle : n * (∑ x : Pick p q n, badColCount B x)
          ≤ (q * n) * (∑ x : Pick p q n, badColCount B x) := by
        apply Nat.mul_le_mul_right
        calc n = 1 * n := (one_mul n).symm
          _ ≤ q * n := Nat.mul_le_mul_right n hq
      exact le_trans hle h
    have hstep : Np * E1a B + Np * E1b B = Np * (E1a B + E1b B) := by ring
    omega
  -- ## the main inequality, before the arithmetic
  have hmain : (Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card * D
      ≤ Np * E0 + Np * (E1a B + E1b B) := by
    refine le_trans hsum1 ?_
    exact Nat.add_le_add_left hline (Np * E0)
  have hcard : (Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card
      + (Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card = Np := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, hcardPick]
  have hnot : S * (Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card
      ≤ Np * E2v := by
    rw [hS, hE2]
    exact card_notGood_le Z B hqn hpn hp hq
  -- ## arithmetic
  have hmulS : S * ((Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card * D)
      ≤ S * (Np * E0 + Np * (E1a B + E1b B)) := Nat.mul_le_mul_left S hmain
  have hmulD : S * ((Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card * D)
      ≤ Np * E2v * D := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right D hnot
  have hE2D := Nat.mul_le_mul_left (Np * E2v) hDS
  have hkey : S * Np * D ≤ S * (Np * E0 + Np * (E1a B + E1b B)) + Np * E2v * S := by
    calc S * Np * D
        = S * ((Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card
            + (Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card) * D := by
          rw [hcard]
      _ = S * ((Finset.univ.filter (fun x : Pick p q n => Good Z B x)).card * D)
            + S * ((Finset.univ.filter (fun x : Pick p q n => ¬ Good Z B x)).card * D) := by
          ring
      _ ≤ S * (Np * E0 + Np * (E1a B + E1b B)) + Np * E2v * D :=
          add_le_add hmulS hmulD
      _ ≤ S * (Np * E0 + Np * (E1a B + E1b B)) + Np * E2v * S :=
          add_le_add (le_refl _) hE2D
  have hkey2 : S * Np * D ≤ S * Np * (E0 + (E1a B + E1b B) + E2v) := by
    refine le_trans hkey (le_of_eq ?_)
    ring
  have hfin : D ≤ E0 + (E1a B + E1b B) + E2v :=
    Nat.le_of_mul_le_mul_left hkey2 (Nat.mul_pos hSpos hNpos)
  -- ## identify the right-hand side with `hamming A⁺ B`
  have hsplit := hamming_blockDiag_split (p := p) (q := q) (n := n) A Z B
  have hgoal : D ≤ Eold A B + E1a B + E1b B + E2 Z B := by
    have h1 : D ≤ E0 + (E1a B + E1b B) + E2v := hfin
    rw [hE0] at h1
    rw [hE2] at h1
    omega
  rw [hsplit]
  exact hgoal

end Lower


/-- A copy of `H` gives a copy of the block diagonal pattern after blowing up the second block. -/
theorem editDist_blockDiag_upper {k l p q n : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hk : 0 < k) (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) (A : BMat n n) :
    editDist (blockDiag H Z) (blockDiag A (blowup Z n)) ≤ editDist H A := by
  obtain ⟨j, hj⟩ := hH.1 ⟨0, hk⟩
  obtain ⟨B, hB, hAB⟩ := _root_.OrderedRemoval.editDist_spec H A
    ⟨zeros n n, free_zero H ⟨⟨0, hk⟩, j, hj⟩⟩
  calc
    editDist (blockDiag H Z) (blockDiag A (blowup Z n))
        ≤ hamming (blockDiag A (blowup Z n)) (blockDiag B (blowup Z n)) :=
      editDist_le _ _ _ (free_blockDiag H Z hH hk hp hq hZ B hB)
    _ = hamming A B := hamming_blockDiag_same A B (blowup Z n)
    _ = editDist H A := hAB

/-- The direct-sum distance equality, with Step 3 proved by finite double counting. -/
theorem editDist_blockDiag_eq {k l p q n : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hk : 0 < k) (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) (A : BMat n n) :
    editDist (blockDiag H Z) (blockDiag A (blowup Z n)) = editDist H A := by
  apply Nat.le_antisymm (editDist_blockDiag_upper H hH hk Z hp hq hZ A)
  obtain ⟨j, hj⟩ := hH.1 ⟨0, hk⟩
  have hHone : ∃ i j, H i j = true := ⟨⟨0, hk⟩, j, hj⟩
  have hplusOne : ∃ i j, blockDiag H Z i j = true := by
    obtain ⟨i, j, hij⟩ := hHone
    exact ⟨Fin.castAdd p i, Fin.castAdd q j, by simp [hij]⟩
  by_cases hn : 0 < n
  · have hfree : ∃ B : BMat (n + p * q * n) (n + p * q * n),
        Free (blockDiag H Z) B :=
      ⟨zeros _ _, free_zero _ hplusOne⟩
    obtain ⟨B, hB, hham⟩ := _root_.OrderedRemoval.editDist_spec
      (blockDiag H Z) (blockDiag A (blowup Z n)) hfree
    rw [← hham]
    exact editDist_le_hamming_of_free H hH hk Z hp hq hn A B hB
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hfreeA : Free H A := by
      rintro ⟨r, c, hr, hc, h⟩
      exact Fin.elim0 (r ⟨0, hk⟩)
    have hfreePlus : Free (blockDiag H Z) (blockDiag A (blowup Z 0)) := by
      rintro ⟨r, c, hr, hc, h⟩
      exact Fin.elim0 (r (Fin.castAdd p ⟨0, hk⟩))
    have hzA : editDist H A = 0 :=
      (_root_.OrderedRemoval.editDist_eq_zero_iff H A ⟨A, hfreeA⟩).2 hfreeA
    have hzPlus : editDist (blockDiag H Z) (blockDiag A (blowup Z 0)) = 0 :=
      (_root_.OrderedRemoval.editDist_eq_zero_iff _ _ ⟨_, hfreePlus⟩).2 hfreePlus
    rw [hzA, hzPlus]

end DirectSumAux

/-! ## 3. Stage 2a: attaching Z = (1) -/

/-- Paper's theorem for `Z = (1)`: `D_{H'}(A⁺) = D_H(A)` with `H' = [H 0; 0 1]`,
`A⁺ = [A 0; 0 J_n]`. -/
theorem editDist_blockDiag_one {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hk : 0 < k) (A : BMat n n) :
    editDist (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) = editDist H A := by
  have h := DirectSumAux.editDist_blockDiag_eq (n := n) H hH hk (ones 1 1)
    (by omega) (by omega) (Or.inl (fun _ _ _ => Subsingleton.elim _ _)) A
  simp only [DirectSumAux.blowup_ones_eq] at h
  rw [show 1 * 1 * n = n by omega] at h
  exact h

/-- Paper's theorem for `Z = (1)`: `N_{H'}(A⁺) ≤ m² N_H(A)` with `m = 2n`. -/
theorem copyCount_blockDiag_one {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (A : BMat n n) :
    copyCount (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) ≤
      (n + n) ^ 2 * copyCount H A := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- degenerate case `k = 0`: `hH` then forces `l = 0`
    subst hk0
    have hl0 : l = 0 := by
      by_contra hl
      obtain ⟨i, -⟩ := hH.2 ⟨0, Nat.pos_of_ne_zero hl⟩
      exact Fin.elim0 i
    subst hl0
    have hH1 : copyCount H A = 1 := by
      have hfilter : (Finset.univ.filter (fun rc : (Fin 0 → Fin n) × (Fin 0 → Fin n) =>
          IsCopy H A rc.1 rc.2)) = Finset.univ := by
        refine Finset.filter_true_of_mem (fun x _ => ?_)
        exact ⟨fun a _ _ => a.elim0, fun a _ _ => a.elim0, fun i => i.elim0⟩
      rw [copyCount, hfilter, Finset.card_univ]
      simp
    rw [hH1, mul_one]
    have h1 := DirectSumAux.copyCount_le (blockDiag H (ones 1 1)) (blockDiag A (ones n n))
    simpa [pow_two] using h1
  · -- main case `0 < k`
    have hl : 0 < l := by
      obtain ⟨j, -⟩ := hH.1 ⟨0, hk⟩
      have := j.isLt
      omega
    -- **(A)** the `H`-rows and `H`-columns of any copy of `[H 0; 0 1]` in `[A 0; 0 J]` are old
    have oldness : ∀ (r : Fin (k + 1) → Fin (n + n)) (c : Fin (l + 1) → Fin (n + n)),
        StrictMono r → StrictMono c →
        (∀ i j, blockDiag A (ones n n) (r i) (c j) = blockDiag H (ones 1 1) i j) →
        (∀ i : Fin k, (r (Fin.castAdd 1 i)).val < n) ∧
          (∀ j : Fin l, (c (Fin.castAdd 1 j)).val < n) := by
      intro r c hr hc hentry
      set k' : Fin k := ⟨k - 1, by omega⟩ with hk'def
      set l' : Fin l := ⟨l - 1, by omega⟩ with hl'def
      constructor
      · intro i
        by_contra hcon
        have hcon' : n ≤ (r (Fin.castAdd 1 i)).val := Nat.le_of_not_lt hcon
        have hik : i ≤ k' := by
          rw [Fin.le_def]; simp only [hk'def, Fin.val_mk]; omega
        have hlastnew : n ≤ (r (Fin.castAdd 1 k')).val := by
          have hmono := hr.monotone (DirectSumAux.castAdd_le_castAdd_iff.mpr hik)
          rw [Fin.le_def] at hmono
          omega
        obtain ⟨j0, hj0⟩ := hH.1 k'
        have hcolnew : n ≤ (c (Fin.castAdd 1 j0)).val := by
          by_contra hcj
          have hcj' : (c (Fin.castAdd 1 j0)).val < n := Nat.lt_of_not_le hcj
          have h1 : blockDiag A (ones n n) (r (Fin.castAdd 1 k')) (c (Fin.castAdd 1 j0))
              = true := by
            rw [hentry (Fin.castAdd 1 k') (Fin.castAdd 1 j0),
              DirectSumAux.blockDiag_castAdd_castAdd, hj0]
          rw [DirectSumAux.blockDiag_apply_new_old A (ones n n) hlastnew hcj'] at h1
          exact Bool.false_ne_true h1
        have hlastcol : n ≤ (c (Fin.natAdd l (0 : Fin 1))).val := by
          have hmono := hc (DirectSumAux.castAdd_lt_natAdd j0 (0 : Fin 1))
          rw [Fin.lt_def] at hmono
          omega
        have h2 : blockDiag A (ones n n) (r (Fin.castAdd 1 k')) (c (Fin.natAdd l (0 : Fin 1)))
            = true :=
          (DirectSumAux.blockDiag_apply_new_new A (ones n n) hlastnew hlastcol).trans
            (DirectSumAux.ones_apply _ _)
        rw [hentry (Fin.castAdd 1 k') (Fin.natAdd l (0 : Fin 1)),
          DirectSumAux.blockDiag_castAdd_natAdd] at h2
        exact Bool.false_ne_true h2
      · intro j
        by_contra hcon
        have hcon' : n ≤ (c (Fin.castAdd 1 j)).val := Nat.le_of_not_lt hcon
        have hjl : j ≤ l' := by
          rw [Fin.le_def]; simp only [hl'def, Fin.val_mk]; omega
        have hlastnew : n ≤ (c (Fin.castAdd 1 l')).val := by
          have hmono := hc.monotone (DirectSumAux.castAdd_le_castAdd_iff.mpr hjl)
          rw [Fin.le_def] at hmono
          omega
        obtain ⟨i0, hi0⟩ := hH.2 l'
        have hrownew : n ≤ (r (Fin.castAdd 1 i0)).val := by
          by_contra hri
          have hri' : (r (Fin.castAdd 1 i0)).val < n := Nat.lt_of_not_le hri
          have h1 : blockDiag A (ones n n) (r (Fin.castAdd 1 i0)) (c (Fin.castAdd 1 l'))
              = true := by
            rw [hentry (Fin.castAdd 1 i0) (Fin.castAdd 1 l'),
              DirectSumAux.blockDiag_castAdd_castAdd, hi0]
          rw [DirectSumAux.blockDiag_apply_old_new A (ones n n) hri' hlastnew] at h1
          exact Bool.false_ne_true h1
        have hlastrow : n ≤ (r (Fin.natAdd k (0 : Fin 1))).val := by
          have hmono := hr (DirectSumAux.castAdd_lt_natAdd i0 (0 : Fin 1))
          rw [Fin.lt_def] at hmono
          omega
        have h2 : blockDiag A (ones n n) (r (Fin.natAdd k (0 : Fin 1))) (c (Fin.castAdd 1 l'))
            = true :=
          (DirectSumAux.blockDiag_apply_new_new A (ones n n) hlastrow hlastnew).trans
            (DirectSumAux.ones_apply _ _)
        rw [hentry (Fin.natAdd k (0 : Fin 1)) (Fin.castAdd 1 l'),
          DirectSumAux.blockDiag_natAdd_castAdd] at h2
        exact Bool.false_ne_true h2
    -- **(B)** a copy of `[H 0; 0 1]` is its `H`-part together with its two new indices
    let oldCopy : {x : (Fin (k + 1) → Fin (n + n)) × (Fin (l + 1) → Fin (n + n)) //
        IsCopy (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) x.1 x.2} →
        {y : (Fin k → Fin n) × (Fin l → Fin n) // IsCopy H A y.1 y.2} :=
      fun x => by
        have ho := oldness x.val.1 x.val.2 x.property.1 x.property.2.1 x.property.2.2
        exact
          ⟨(fun i => ⟨(x.val.1 (Fin.castAdd 1 i)).val, ho.1 i⟩,
            fun j => ⟨(x.val.2 (Fin.castAdd 1 j)).val, ho.2 j⟩),
          ⟨fun i j hij => Fin.lt_def.mp (x.property.1 (DirectSumAux.castAdd_lt_castAdd_iff.mpr hij)),
            fun i j hij => Fin.lt_def.mp (x.property.2.1 (DirectSumAux.castAdd_lt_castAdd_iff.mpr hij)),
            fun i j =>
              (DirectSumAux.blockDiag_apply_old_old A (ones n n) (ho.1 i) (ho.2 j)).symm.trans
                (by
                  have h := x.property.2.2 (Fin.castAdd 1 i) (Fin.castAdd 1 j)
                  rw [DirectSumAux.blockDiag_castAdd_castAdd] at h
                  exact h)⟩⟩
    let split : {x : (Fin (k + 1) → Fin (n + n)) × (Fin (l + 1) → Fin (n + n)) //
        IsCopy (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) x.1 x.2} →
        {y : (Fin k → Fin n) × (Fin l → Fin n) // IsCopy H A y.1 y.2} ×
          ((Fin 1 → Fin (n + n)) × (Fin 1 → Fin (n + n))) :=
      fun x => (oldCopy x,
        (fun i => x.val.1 (Fin.natAdd k i), fun j => x.val.2 (Fin.natAdd l j)))
    have hsplit : Function.Injective split := by
      rintro ⟨⟨r, c⟩, hrc⟩ ⟨⟨r', c'⟩, hrc'⟩ hEq
      have h1 : (split ⟨⟨r, c⟩, hrc⟩).1 = (split ⟨⟨r', c'⟩, hrc'⟩).1 := congrArg Prod.fst hEq
      have h2 : (split ⟨⟨r, c⟩, hrc⟩).2 = (split ⟨⟨r', c'⟩, hrc'⟩).2 := congrArg Prod.snd hEq
      have hrowval : ∀ i : Fin k,
          ((oldCopy ⟨⟨r, c⟩, hrc⟩).val.1 i).val = ((oldCopy ⟨⟨r', c'⟩, hrc'⟩).val.1 i).val :=
        fun i => congrArg (fun z => ((z.val.1) i).val) h1
      have hcolval : ∀ j : Fin l,
          ((oldCopy ⟨⟨r, c⟩, hrc⟩).val.2 j).val = ((oldCopy ⟨⟨r', c'⟩, hrc'⟩).val.2 j).val :=
        fun j => congrArg (fun z => ((z.val.2) j).val) h1
      have hnewrow : ∀ i : Fin 1, r (Fin.natAdd k i) = r' (Fin.natAdd k i) :=
        fun i => congrFun (congrArg Prod.fst h2) i
      have hnewcol : ∀ j : Fin 1, c (Fin.natAdd l j) = c' (Fin.natAdd l j) :=
        fun j => congrFun (congrArg Prod.snd h2) j
      have hreq : r = r' := by
        funext z
        obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := DirectSumAux.eq_castAdd_or_natAdd z
        · exact Fin.ext (hrowval i)
        · exact hnewrow i
      have hceq : c = c' := by
        funext z
        obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := DirectSumAux.eq_castAdd_or_natAdd z
        · exact Fin.ext (hcolval j)
        · exact hnewcol j
      exact Subtype.ext (Prod.ext hreq hceq)
    -- **(C)** counting the injection
    have hCS : Fintype.card {x : (Fin (k + 1) → Fin (n + n)) × (Fin (l + 1) → Fin (n + n)) //
        IsCopy (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) x.1 x.2}
        = copyCount (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) := by
      rw [copyCount, Fintype.card_subtype]
    have hHC : Fintype.card {y : (Fin k → Fin n) × (Fin l → Fin n) //
        IsCopy H A y.1 y.2} = copyCount H A := by
      rw [copyCount, Fintype.card_subtype]
    have hinj := Fintype.card_le_of_injective split hsplit
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_one] at hinj
    rw [hHC] at hinj
    calc copyCount (blockDiag H (ones 1 1)) (blockDiag A (ones n n))
        = Fintype.card {x : (Fin (k + 1) → Fin (n + n)) × (Fin (l + 1) → Fin (n + n)) //
            IsCopy (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) x.1 x.2} := hCS.symm
      _ ≤ copyCount H A * ((n + n) * (n + n)) := hinj
      _ = (n + n) ^ 2 * copyCount H A := by ring

namespace ZeroColsAux

open Classical

variable {k l n : ℕ}

/-- An old row index of `A⁺ = [A 0; 0 0]`, of size `(1+q)n`. -/
abbrev orow (n q : ℕ) (i : Fin n) : Fin (n + q * n) := Fin.castAdd (q * n) i

/-- A new column index of `A⁺ = [A 0; 0 0]`. -/
abbrev ocol (n q : ℕ) (c : Fin (q * n)) : Fin (n + q * n) := Fin.natAdd n c

/-- The `t`-th column of the `j`-th group of `n` new columns. -/
abbrev gcol (q n : ℕ) (j : Fin q) (t : Fin n) : Fin (q * n) := finProdFinEquiv (j, t)

/-- The same, as an index of the host. -/
abbrev ncol (n q : ℕ) (j : Fin q) (t : Fin n) : Fin (n + q * n) := Fin.natAdd n (gcol q n j t)

theorem gcol_val (j : Fin q) (t : Fin n) : (gcol q n j t).val = t.val + n * j.val := rfl

theorem gcol_lt_gcol {j j' : Fin q} (h : j < j') (t t' : Fin n) :
    gcol q n j t < gcol q n j' t' := by
  rw [Fin.lt_def, gcol_val, gcol_val, Nat.mul_comm n j.val, Nat.mul_comm n j'.val]
  have h1 : j.val + 1 ≤ j'.val := h
  have hle : (j.val + 1) * n ≤ j'.val * n := Nat.mul_le_mul_right n h1
  have hlt : t.val + j.val * n < (j.val + 1) * n := by rw [Nat.succ_mul]; omega
  omega

/-- The picked columns, in increasing order. -/
theorem strictMono_ncol (γ : Fin q → Fin n) : StrictMono fun j => ncol n q j (γ j) :=
  DirectSumAux.strictMono_natAdd_comp (fun a b hab => gcol_lt_gcol hab (γ a) (γ b)) n

/-- Summing over the new columns is summing over the `q` groups of `n` columns. -/
theorem sum_gcol {M : Type*} [AddCommMonoid M] (f : Fin (q * n) → M) :
    (∑ j : Fin q, ∑ t : Fin n, f (gcol q n j t)) = ∑ c : Fin (q * n), f c := by
  rw [← Fintype.sum_prod_type (f := fun x : Fin q × Fin n => f (gcol q n x.1 x.2))]
  exact Fintype.sum_equiv finProdFinEquiv (fun x : Fin q × Fin n => f (gcol q n x.1 x.2)) f
    (fun x => rfl)

/-- `B` has a `1` in old row `r` under one of the picked new columns. -/
def Bad (B : BMat (n + q * n) (n + q * n)) (γ : Fin q → Fin n) (r : Fin n) : Prop :=
  ∃ j : Fin q, B (orow n q r) (ncol n q j (γ j)) = true

/-- The number of bad old rows of a pick. -/
noncomputable def badCount (B : BMat (n + q * n) (n + q * n)) (γ : Fin q → Fin n) : ℕ :=
  ∑ r : Fin n, if Bad B γ r then 1 else 0

/-- The old-old block of `B` with the bad rows replaced by zeros (`B°` of the paper). -/
noncomputable def Bzero (B : BMat (n + q * n) (n + q * n)) (γ : Fin q → Fin n) : BMat n n :=
  fun r c => if Bad B γ r then false else B (orow n q r) (orow n q c)

theorem Bzero_of_not_bad (B : BMat (n + q * n) (n + q * n)) (γ : Fin q → Fin n)
    {r : Fin n} (h : ¬ Bad B γ r) (c : Fin n) :
    Bzero B γ r c = B (orow n q r) (orow n q c) := by
  simp only [Bzero]; rw [if_neg h]

theorem Bzero_of_bad (B : BMat (n + q * n) (n + q * n)) (γ : Fin q → Fin n)
    {r : Fin n} (h : Bad B γ r) (c : Fin n) : Bzero B γ r c = false := by
  simp only [Bzero]; rw [if_pos h]

/-- **The claim of Step 3.**  If the pick's rows are not bad, a copy of `H` in `B°` together
with the picked columns is a copy of `H' = [H 0]` in `B`. -/
theorem free_Bzero (H : BMat k l) (hH : NoZeroLine H) (B : BMat (n + q * n) (n + q * n))
    (hB : Free (appendZeroCols H q) B) (γ : Fin q → Fin n) : Free H (Bzero B γ) := by
  refine DirectSumAux.free_of_no_copy (fun r c hcopy => ?_)
  obtain ⟨hr, hc, hrc⟩ := hcopy
  have hnb : ∀ i : Fin k, ¬ Bad B γ (r i) := by
    intro i hbad
    obtain ⟨j, hj⟩ := hH.1 i
    have h1 := Bzero_of_bad B γ hbad (c j)
    rw [hrc i j, hj] at h1
    exact absurd h1 (by simp)
  refine hB ⟨fun i => orow n q (r i),
    Fin.append (fun j => orow n q (c j)) (fun j => ncol n q j (γ j)), ?_, ?_, ?_⟩
  · exact DirectSumAux.strictMono_castAdd_comp hr
  · exact DirectSumAux.strictMono_append (DirectSumAux.strictMono_castAdd_comp hc)
      (strictMono_ncol γ) (fun i j => DirectSumAux.castAdd_lt_natAdd _ _)
  · intro i jj
    obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := DirectSumAux.eq_castAdd_or_natAdd jj
    · rw [Fin.append_left, DirectSumAux.appendZeroCols_castAdd,
        (Bzero_of_not_bad B γ (hnb i) (c j)).symm, hrc i j]
    · rw [Fin.append_right, DirectSumAux.appendZeroCols_natAdd]
      have hne : B (orow n q (r i)) (ncol n q j (γ j)) ≠ true := fun hc' => hnb i ⟨j, hc'⟩
      cases hbb : B (orow n q (r i)) (ncol n q j (γ j))
      · rfl
      · exact absurd hbb hne

/-- **`D ≤ E₀ + n · (number of bad rows)`** for a fixed pick. -/
theorem indicator_Bzero_le (A : BMat n n) (B : BMat (n + q * n) (n + q * n))
    (γ : Fin q → Fin n) (r c : Fin n) :
    (if A r c ≠ Bzero B γ r c then 1 else 0) ≤
      (if A r c ≠ B (orow n q r) (orow n q c) then 1 else 0)
        + (if Bad B γ r then 1 else 0) := by
  by_cases h : Bad B γ r
  · rw [Bzero_of_bad B γ h]
    have h1 : (if A r c ≠ false then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
    have h2 : (1 : ℕ) ≤ (if Bad B γ r then 1 else 0) := by rw [if_pos h]
    omega
  · rw [Bzero_of_not_bad B γ h, if_neg h, Nat.add_zero]

theorem hamming_Bzero_le (A : BMat n n) (B : BMat (n + q * n) (n + q * n))
    (γ : Fin q → Fin n) :
    hamming A (Bzero B γ) ≤ hamming A (fun r c => B (orow n q r) (orow n q c))
      + n * badCount B γ := by
  rw [DirectSumAux.hamming_double_sum (A := A) (B := Bzero B γ),
    DirectSumAux.hamming_double_sum (A := A) (B := fun r c => B (orow n q r) (orow n q c)),
    badCount]
  have hstep : (∑ r : Fin n, ∑ c : Fin n, (if A r c ≠ Bzero B γ r c then 1 else 0))
      ≤ ∑ r : Fin n, ∑ c : Fin n,
          ((if A r c ≠ B (orow n q r) (orow n q c) then 1 else 0)
            + (if Bad B γ r then 1 else 0)) :=
    Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun c _ => indicator_Bzero_le A B γ r c))
  refine le_trans hstep ?_
  have hsplit : ∀ r : Fin n,
      (∑ c : Fin n, ((if A r c ≠ B (orow n q r) (orow n q c) then 1 else 0)
            + (if Bad B γ r then 1 else 0)))
        = (∑ c : Fin n, (if A r c ≠ B (orow n q r) (orow n q c) then 1 else 0))
          + (if Bad B γ r then n else 0) := by
    intro r
    rw [Finset.sum_add_distrib]
    have hconst : (∑ _c : Fin n, (if Bad B γ r then 1 else 0)) = (if Bad B γ r then n else 0) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      split <;> simp
    rw [hconst]
  rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib]
  have hlast : (∑ r : Fin n, (if Bad B γ r then n else 0))
      = n * (∑ r : Fin n, (if Bad B γ r then 1 else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split <;> simp
  rw [hlast]

/-- The `1`s of the old-row/new-column block of `B`, grouped by column group. -/
noncomputable def E1 (B : BMat (n + q * n) (n + q * n)) : ℕ :=
  ∑ r : Fin n, ∑ j : Fin q, ∑ t : Fin n,
    (if B (orow n q r) (ncol n q j t) = true then 1 else 0)

/-- **The double count.**  A `1` of the old-row/new-column block is met by a picked column with
probability `1/n`, so `n · Σ_γ (bad rows of γ) ≤ n^q · E₁`. -/
theorem sum_badCount_le (B : BMat (n + q * n) (n + q * n)) (hq : 0 < q) :
    n * (∑ γ : Fin q → Fin n, badCount B γ) ≤ n ^ q * E1 B := by
  classical
  have hstep1 : (∑ γ : Fin q → Fin n, badCount B γ)
      ≤ ∑ γ : Fin q → Fin n, ∑ r : Fin n, ∑ j : Fin q,
          (if B (orow n q r) (ncol n q j (γ j)) = true then 1 else 0) := by
    refine Finset.sum_le_sum (fun γ _ => ?_)
    rw [badCount]
    refine Finset.sum_le_sum (fun r _ => ?_)
    by_cases h : Bad B γ r
    · rw [if_pos h]
      obtain ⟨j0, hj0⟩ := h
      have hsingle := Finset.single_le_sum
        (f := fun j : Fin q => (if B (orow n q r) (ncol n q j (γ j)) = true then 1 else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      rw [if_pos hj0] at hsingle
      exact hsingle
    · rw [if_neg h]; exact Nat.zero_le _
  refine le_trans (Nat.mul_le_mul_left n hstep1) ?_
  have hswap : (∑ γ : Fin q → Fin n, ∑ r : Fin n, ∑ j : Fin q,
        (if B (orow n q r) (ncol n q j (γ j)) = true then 1 else 0))
      = ∑ r : Fin n, ∑ j : Fin q, ∑ γ : Fin q → Fin n,
        (if B (orow n q r) (ncol n q j (γ j)) = true then 1 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)
  rw [hswap]
  have hval : ∀ (r : Fin n) (j : Fin q),
      (∑ γ : Fin q → Fin n, (if B (orow n q r) (ncol n q j (γ j)) = true then 1 else 0))
        = n ^ (q - 1) *
            (∑ t : Fin n, (if B (orow n q r) (ncol n q j t) = true then 1 else 0)) := by
    intro r j
    exact DirectSumAux.sum_fibre_eval (p := q) n j
      (fun t => if B (orow n q r) (ncol n q j t) = true then 1 else 0)
  rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => hval r j))]
  have hpull : (∑ r : Fin n, ∑ j : Fin q, n ^ (q - 1) *
        (∑ t : Fin n, (if B (orow n q r) (ncol n q j t) = true then 1 else 0)))
      = n ^ (q - 1) * E1 B := by
    simp only [E1, Finset.mul_sum]
  rw [hpull]
  have hpow : n * n ^ (q - 1) = n ^ q := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  rw [← hpow, mul_assoc]

/-- **`hamming A B° ≤ E₀ + n · (bad rows)`** in the `E₁` notation. -/
theorem hamming_A_Bzero_le (A : BMat n n) (B : BMat (n + q * n) (n + q * n))
    (γ : Fin q → Fin n) :
    hamming A (Bzero B γ) ≤ hamming A (fun r c => B (orow n q r) (orow n q c))
      + n * badCount B γ := hamming_Bzero_le A B γ

/-- Splitting `hamming A⁺ B` into its four blocks. -/
theorem hamming_blockDiag_zeros_split (A : BMat n n) (B : BMat (n + q * n) (n + q * n)) :
    hamming (blockDiag A (zeros (q * n) (q * n))) B
      = hamming A (fun r c => B (orow n q r) (orow n q c))
        + (∑ r : Fin n, ∑ c : Fin (q * n),
            (if false ≠ B (orow n q r) (ocol n q c) then 1 else 0))
        + (∑ c : Fin (q * n), ∑ r : Fin n,
            (if false ≠ B (ocol n q c) (orow n q r) then 1 else 0))
        + (∑ c : Fin (q * n), ∑ c' : Fin (q * n),
            (if false ≠ B (ocol n q c) (ocol n q c') then 1 else 0)) := by
  rw [DirectSumAux.hamming_double_sum (A := blockDiag A (zeros (q * n) (q * n))) (B := B),
    DirectSumAux.sum_four_blocks (F := fun i j =>
      if blockDiag A (zeros (q * n) (q * n)) i j ≠ B i j then 1 else 0)]
  simp only [orow, ocol, DirectSumAux.blockDiag_old_old, DirectSumAux.blockDiag_old_new,
    DirectSumAux.blockDiag_new_old, DirectSumAux.blockDiag_new_new, DirectSumAux.zeros_apply]
  rw [DirectSumAux.hamming_double_sum (A := A)
    (B := fun r c => B (Fin.castAdd (q * n) r) (Fin.castAdd (q * n) c))]

/-- The old-old block of `B` is at distance at most `hamming A⁺ B` from `A`. -/
theorem hamming_le_hamming_blockDiag (A : BMat n n) (B : BMat (n + q * n) (n + q * n)) :
    hamming A (fun r c => B (orow n q r) (orow n q c))
      ≤ hamming (blockDiag A (zeros (q * n) (q * n))) B := by
  have hsplit := hamming_blockDiag_zeros_split A B
  rw [hsplit]
  omega

/-- **`E₁` is at most the old-row/new-column block of `hamming A⁺ B`.** -/
theorem E1_le_mixed (B : BMat (n + q * n) (n + q * n)) :
    E1 B ≤ ∑ r : Fin n, ∑ c : Fin (q * n),
      (if false ≠ B (orow n q r) (ocol n q c) then 1 else 0) := by
  have h1 : (∑ r : Fin n, ∑ c : Fin (q * n),
        (if false ≠ B (orow n q r) (ocol n q c) then 1 else 0))
      = ∑ r : Fin n, ∑ j : Fin q, ∑ t : Fin n,
        (if false ≠ B (orow n q r) (ncol n q j t) then 1 else 0) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    exact (sum_gcol (q := q) (n := n)
      (fun c => if false ≠ B (orow n q r) (ocol n q c) then 1 else 0)).symm
  rw [h1, E1]
  refine Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ =>
    Finset.sum_le_sum (fun t _ => ?_)))
  by_cases hc : B (orow n q r) (ncol n q j t) = true
  · rw [if_pos hc, if_pos (by rw [hc]; exact Bool.false_ne_true)]
  · rw [if_neg hc]
    split <;> omega

/-- **`E₀ + E₁ ≤ hamming A⁺ B`.** -/
theorem hamming_ge (A : BMat n n) (B : BMat (n + q * n) (n + q * n)) :
    hamming A (fun r c => B (orow n q r) (orow n q c)) + E1 B
      ≤ hamming (blockDiag A (zeros (q * n) (q * n))) B := by
  have hsplit := hamming_blockDiag_zeros_split A B
  have h := E1_le_mixed B
  rw [hsplit]
  omega

/-- **Step 3 for a fixed `H'`-free `B`**, main case `0 < n`, `0 < q`. -/
theorem per_pick (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k) (A : BMat n n)
    (B : BMat (n + q * n) (n + q * n)) (hB : Free (appendZeroCols H q) B)
    (γ : Fin q → Fin n) :
    editDist H A ≤ hamming A (fun r c => B (orow n q r) (orow n q c)) + n * badCount B γ := by
  have hl : 0 < l := lt_of_noZeroLine H hH hk
  have hfree : ∃ B' : BMat n n, Free H B' := exists_free H hk hl n n
  exact le_trans (editDist_le H A _ (free_Bzero H hH B hB γ)) (hamming_Bzero_le A B γ)

theorem lower_main (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k) (hn : 0 < n) (hq : 0 < q)
    (A : BMat n n) (B : BMat (n + q * n) (n + q * n))
    (hB : Free (appendZeroCols H q) B) :
    editDist H A ≤ hamming (blockDiag A (zeros (q * n) (q * n))) B := by
  classical
  have hsum : (∑ _γ : Fin q → Fin n, editDist H A)
      ≤ ∑ γ : Fin q → Fin n,
          (hamming A (fun r c => B (orow n q r) (orow n q c)) + n * badCount B γ) :=
    Finset.sum_le_sum (fun γ _ => per_pick H hH hk A B hB γ)
  have hcard : (∑ _γ : Fin q → Fin n, editDist H A) = n ^ q * editDist H A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul]
  rw [hcard, Finset.sum_add_distrib] at hsum
  have hconst : (∑ _γ : Fin q → Fin n,
        hamming A (fun r c => B (orow n q r) (orow n q c)))
      = n ^ q * hamming A (fun r c => B (orow n q r) (orow n q c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul]
  rw [hconst] at hsum
  have hcnt : n * (∑ γ : Fin q → Fin n, badCount B γ) ≤ n ^ q * E1 B := sum_badCount_le B hq
  have hpos : 0 < n ^ q := pow_pos hn q
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have hstep : (∑ γ : Fin q → Fin n, n * badCount B γ)
      = n * (∑ γ : Fin q → Fin n, badCount B γ) := (Finset.mul_sum _ _ _).symm
  rw [hstep] at hsum
  have hge := hamming_ge A B
  calc n ^ q * editDist H A
      ≤ n ^ q * hamming A (fun r c => B (orow n q r) (orow n q c))
          + n * (∑ γ : Fin q → Fin n, badCount B γ) := hsum
    _ ≤ n ^ q * hamming A (fun r c => B (orow n q r) (orow n q c)) + n ^ q * E1 B :=
        Nat.add_le_add_left hcnt _
    _ = n ^ q * (hamming A (fun r c => B (orow n q r) (orow n q c)) + E1 B) := by ring
    _ ≤ n ^ q * hamming (blockDiag A (zeros (q * n) (q * n))) B :=
        Nat.mul_le_mul_left _ hge

/-- **Step 3, degenerate case `q = 0`**: no picks are needed. -/
theorem lower_zero (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (A : BMat n n) (B : BMat (n + 0 * n) (n + 0 * n))
    (hB : Free (appendZeroCols H 0) B) :
    editDist H A ≤ hamming (blockDiag A (zeros (0 * n) (0 * n))) B := by
  classical
  have hl : 0 < l := lt_of_noZeroLine H hH hk
  have hfree : ∃ B' : BMat n n, Free H B' := exists_free H hk hl n n
  have hbad : ∀ r : Fin n, ¬ Bad B (Fin.elim0 : Fin 0 → Fin n) r := by
    rintro r ⟨j, -⟩
    exact j.elim0
  have h1 : editDist H A ≤ hamming A (Bzero B (Fin.elim0 : Fin 0 → Fin n)) :=
    editDist_le H A _ (free_Bzero H hH B hB _)
  have h2 : hamming A (Bzero B (Fin.elim0 : Fin 0 → Fin n))
      ≤ hamming A (fun r c => B (orow n 0 r) (orow n 0 c)) := by
    have h := hamming_Bzero_le (q := 0) A B (Fin.elim0 : Fin 0 → Fin n)
    have hz : badCount B (Fin.elim0 : Fin 0 → Fin n) = 0 := by
      rw [badCount]
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [if_neg (hbad r)]
    rw [hz, Nat.mul_zero, add_zero] at h
    exact h
  exact le_trans h1 (le_trans h2 (hamming_le_hamming_blockDiag A B))

/-- `editDist H A = 0` when no `H`-free matrix of that shape exists. -/
theorem editDist_eq_zero_of_no_free {N M : ℕ} (H : BMat k l) (A : BMat N M)
    (h : ¬ ∃ B : BMat N M, Free H B) : editDist H A = 0 := by
  have hempty : {d : ℕ | ∃ B : BMat N M, Free H B ∧ hamming A B = d} = ∅ := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro B hB _
    exact h ⟨B, hB⟩
  rw [editDist, hempty, Nat.sInf_empty]

/-- A host with no rows contains no pattern with a row. -/
theorem free_of_host_rows_zero (H : BMat k l) (hk : 0 < k) (A : BMat 0 m) : Free H A := by
  refine DirectSumAux.free_of_no_copy (fun r _ _ => ?_)
  exact absurd (r ⟨0, hk⟩).isLt (Nat.not_lt_zero _)

/-- `NoZeroLine` and one empty dimension force both to be empty. -/
theorem eq_zero_of_noZeroLine {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (h : k = 0 ∨ l = 0) : k = 0 ∧ l = 0 := by
  rcases h with hk | hl
  · subst hk
    refine ⟨rfl, ?_⟩
    by_contra hl
    obtain ⟨i, -⟩ := hH.2 ⟨0, Nat.pos_of_ne_zero hl⟩
    exact Fin.elim0 i
  · subst hl
    refine ⟨?_, rfl⟩
    by_contra hk
    obtain ⟨j, -⟩ := hH.1 ⟨0, Nat.pos_of_ne_zero hk⟩
    exact Fin.elim0 j

/-- A pattern with no rows and at most `M` columns sits in every host with `M` columns. -/
theorem contains_zero_rows (P : BMat 0 Q) (h : Q ≤ M) (B : BMat N M) : Contains P B := by
  refine ⟨Fin.elim0, fun j => Fin.castLE h j, ?_, ?_, ?_⟩
  · intro a; exact a.elim0
  · intro a b hab
    exact hab
  · intro i; exact i.elim0

/-- A pattern with no rows is never a distance away: `editDist` is `0`. -/
theorem editDist_zero_rows (P : BMat 0 Q) (B : BMat N M) : editDist P B = 0 := by
  by_cases h : Q ≤ M
  · refine editDist_eq_zero_of_no_free P B (fun hex => ?_)
    obtain ⟨B', hB'⟩ := hex
    exact hB' (contains_zero_rows P h B')
  · have hfree : Free P B := by
      refine DirectSumAux.free_of_no_copy (fun r c hcopy => ?_)
      have hinj : Function.Injective c := hcopy.2.1.injective
      have hcle := Fintype.card_le_of_injective c hinj
      simp only [Fintype.card_fin] at hcle
      omega
    exact (editDist_eq_zero_iff P B ⟨B, hfree⟩).2 hfree

/-- **Step 1 for the upper bound.**  A copy of `H' = [H 0]` in `[B 0; 0 0]` restricts to a copy
of `H` in `B`: every row of `H` has a `1`, so no row of the copy is new, and then no `H`-column of
the copy is new either. -/
theorem free_blockDiag_zeros (H : BMat k l) (hH : NoZeroLine H) (B : BMat n n)
    (hB : Free H B) (q : ℕ) :
    Free (appendZeroCols H q) (blockDiag B (zeros (q * n) (q * n))) := by
  classical
  refine DirectSumAux.free_of_no_copy (fun r c hcopy => ?_)
  obtain ⟨hr, hc, hrc⟩ := hcopy
  have hrow : ∀ i : Fin k, (r i).val < n := by
    intro i
    obtain ⟨j, hj⟩ := hH.1 i
    have hentry : blockDiag B (zeros (q * n) (q * n)) (r i) (c (Fin.castAdd q j)) = true := by
      rw [hrc i (Fin.castAdd q j), DirectSumAux.appendZeroCols_castAdd, hj]
    by_contra hcon
    have hge : n ≤ (r i).val := Nat.le_of_not_lt hcon
    obtain ⟨i', hi'⟩ : ∃ i' : Fin (q * n), r i = Fin.natAdd n i' :=
      ⟨⟨(r i).val - n, by have := (r i).isLt; omega⟩, DirectSumAux.natAdd_of_val_ge hge⟩
    rw [hi'] at hentry
    obtain ⟨j', hj'⟩ | ⟨j', hj'⟩ := DirectSumAux.eq_castAdd_or_natAdd (c (Fin.castAdd q j))
    · rw [hj', DirectSumAux.blockDiag_new_old] at hentry
      exact Bool.false_ne_true hentry
    · rw [hj', DirectSumAux.blockDiag_new_new, DirectSumAux.zeros_apply] at hentry
      exact Bool.false_ne_true hentry
  have hcol : ∀ j : Fin l, (c (Fin.castAdd q j)).val < n := by
    intro j
    obtain ⟨i, hi⟩ := hH.2 j
    have hentry : blockDiag B (zeros (q * n) (q * n)) (r i) (c (Fin.castAdd q j)) = true := by
      rw [hrc i (Fin.castAdd q j), DirectSumAux.appendZeroCols_castAdd, hi]
    by_contra hcon
    have hge : n ≤ (c (Fin.castAdd q j)).val := Nat.le_of_not_lt hcon
    obtain ⟨j', hj'⟩ : ∃ j' : Fin (q * n), c (Fin.castAdd q j) = Fin.natAdd n j' :=
      ⟨⟨(c (Fin.castAdd q j)).val - n, by have := (c (Fin.castAdd q j)).isLt; omega⟩,
        DirectSumAux.natAdd_of_val_ge hge⟩
    obtain ⟨i', hi'⟩ : ∃ i' : Fin n, r i = Fin.castAdd (q * n) i' :=
      ⟨⟨(r i).val, hrow i⟩, DirectSumAux.castAdd_of_val_lt (hrow i)⟩
    rw [hi', hj', DirectSumAux.blockDiag_old_new] at hentry
    exact Bool.false_ne_true hentry
  refine hB ⟨fun i => ⟨(r i).val, hrow i⟩, fun j => ⟨(c (Fin.castAdd q j)).val, hcol j⟩,
    ?_, ?_, ?_⟩
  · intro a b hab
    exact hr hab
  · intro a b hab
    exact hc (by rwa [DirectSumAux.castAdd_lt_castAdd_iff])
  · intro i j
    have he := hrc i (Fin.castAdd q j)
    rw [DirectSumAux.appendZeroCols_castAdd] at he
    rw [show r i = Fin.castAdd (q * n) (⟨(r i).val, hrow i⟩ : Fin n) from Fin.ext rfl,
      show c (Fin.castAdd q j) = Fin.castAdd (q * n)
        (⟨(c (Fin.castAdd q j)).val, hcol j⟩ : Fin n) from Fin.ext rfl,
      DirectSumAux.blockDiag_old_old] at he
    exact he

/-- **Step 2: `D_{H'}(A⁺) ≤ D_H(A)`.** -/
theorem upper (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k) (A : BMat n n) (q : ℕ) :
    editDist (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) ≤ editDist H A := by
  obtain ⟨j, hj⟩ := hH.1 ⟨0, hk⟩
  obtain ⟨B, hB, hAB⟩ := editDist_spec H A ⟨zeros n n, free_zero H ⟨⟨0, hk⟩, j, hj⟩⟩
  calc editDist (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n)))
      ≤ hamming (blockDiag A (zeros (q * n) (q * n)))
          (blockDiag B (zeros (q * n) (q * n))) :=
        editDist_le _ _ _ (free_blockDiag_zeros H hH B hB q)
    _ = hamming A B := DirectSumAux.hamming_blockDiag_same A B (zeros (q * n) (q * n))
    _ = editDist H A := hAB

end ZeroColsAux

/-! ## 4. Stage 2b: appending zero columns (the paper's Variant) -/

/-- Variant: `H' = [H 0^{k×q}]`, `A⁺ = [A 0; 0 0]` of size `(1+q)n`. -/
theorem editDist_appendZeroCols {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ)
    (A : BMat n n) :
    editDist (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) = editDist H A := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0` forces `l = 0`, and then both sides are `0`
    obtain ⟨hk0', hl0⟩ := ZeroColsAux.eq_zero_of_noZeroLine H hH (Or.inl hk0)
    subst hk0'
    subst hl0
    rw [ZeroColsAux.editDist_zero_rows (appendZeroCols H q)
          (blockDiag A (zeros (q * n) (q * n))),
      ZeroColsAux.editDist_zero_rows H A]
  · rcases Nat.eq_zero_or_pos n with hn0 | hn
    · -- `n = 0`: both hosts have no rows
      subst hn0
      have hfreeA : Free H A := ZeroColsAux.free_of_host_rows_zero H hk A
      have hfreeM : Free (appendZeroCols H q) (blockDiag A (zeros (q * 0) (q * 0))) :=
        ZeroColsAux.free_of_host_rows_zero _ hk _
      have h1 : editDist H A = 0 := (editDist_eq_zero_iff H A ⟨A, hfreeA⟩).2 hfreeA
      have h2 : editDist (appendZeroCols H q) (blockDiag A (zeros (q * 0) (q * 0))) = 0 :=
        (editDist_eq_zero_iff _ _ ⟨_, hfreeM⟩).2 hfreeM
      rw [h1, h2]
    · refine Nat.le_antisymm (ZeroColsAux.upper H hH hk A q) ?_
      by_cases hfree : ∃ B : BMat (n + q * n) (n + q * n), Free (appendZeroCols H q) B
      · obtain ⟨B, hB, hMB⟩ :=
          editDist_spec (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) hfree
        rw [← hMB]
        rcases Nat.eq_zero_or_pos q with hq0 | hq
        · subst hq0
          exact ZeroColsAux.lower_zero H hH hk A B hB
        · exact ZeroColsAux.lower_main H hH hk hn hq A B hB
      · -- impossible: the zero matrix is `[H 0]`-free, since `H` has a `1`
        obtain ⟨j, hj⟩ := hH.1 ⟨0, hk⟩
        exact absurd ⟨zeros _ _, free_zero (appendZeroCols H q)
          ⟨⟨0, hk⟩, Fin.castAdd q j, by rw [DirectSumAux.appendZeroCols_castAdd, hj]⟩⟩ hfree

/-! ### `N` for the zero-column variant, by restricting a copy -/

section AppendZeroColsCount

/-- In a copy of `[H 0^{k×q}]` inside `[A 0; 0 0]`, a `1` of `H` forces its row and its own
column to be old: the mixed blocks and the appended block of the host are all zero. -/
theorem m3_true_entry_old {k l n q : ℕ} {H : BMat k l} {A : BMat n n}
    {r : Fin k → Fin (n + q * n)} {c : Fin (l + q) → Fin (n + q * n)}
    (h : IsCopy (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) r c)
    {i : Fin k} {j : Fin l} (hij : H i j = true) :
    (r i).val < n ∧ (c (Fin.castAdd q j)).val < n := by
  have hentry : blockDiag A (zeros (q * n) (q * n)) (r i) (c (Fin.castAdd q j)) = true := by
    rw [h.2.2 i (Fin.castAdd q j), DirectSumAux.appendZeroCols_castAdd]
    exact hij
  have hrow : (r i).val < n := by
    by_contra hcon
    have hge : n ≤ (r i).val := not_lt.mp hcon
    rcases Nat.lt_or_ge (c (Fin.castAdd q j)).val n with hclt | hcge
    · rw [DirectSumAux.blockDiag_apply_new_old A (zeros (q * n) (q * n)) hge hclt] at hentry
      exact Bool.false_ne_true hentry
    · rw [DirectSumAux.blockDiag_apply_new_new A (zeros (q * n) (q * n)) hge hcge] at hentry
      exact Bool.false_ne_true hentry
  refine ⟨hrow, ?_⟩
  by_contra hcon
  have hge : n ≤ (c (Fin.castAdd q j)).val := not_lt.mp hcon
  rw [DirectSumAux.blockDiag_apply_old_new A (zeros (q * n) (q * n)) hrow hge] at hentry
  exact Bool.false_ne_true hentry

/-- The rows of such a copy are old. -/
theorem m3_row_old {k l n q : ℕ} {H : BMat k l} (hH : NoZeroLine H) {A : BMat n n}
    {r : Fin k → Fin (n + q * n)} {c : Fin (l + q) → Fin (n + q * n)}
    (h : IsCopy (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) r c) (i : Fin k) :
    (r i).val < n :=
  (m3_true_entry_old h (hH.1 i).choose_spec).1

/-- The columns carrying `H` in such a copy are old. -/
theorem m3_col_old {k l n q : ℕ} {H : BMat k l} (hH : NoZeroLine H) {A : BMat n n}
    {r : Fin k → Fin (n + q * n)} {c : Fin (l + q) → Fin (n + q * n)}
    (h : IsCopy (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) r c) (j : Fin l) :
    (c (Fin.castAdd q j)).val < n :=
  (m3_true_entry_old h (hH.2 j).choose_spec).2

/-- The copies of `[H 0^{k×q}]` in `[A 0; 0 0]`, as a type. -/
abbrev m3CopySet {k l n : ℕ} (H : BMat k l) (A : BMat n n) (q : ℕ) : Type :=
  {rc : (Fin k → Fin (n + q * n)) × (Fin (l + q) → Fin (n + q * n)) //
    IsCopy (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) rc.1 rc.2}

/-- The copies of `H` in `A`, as a type. -/
abbrev m3HCopySet {k l n : ℕ} (H : BMat k l) (A : BMat n n) : Type :=
  {rc : (Fin k → Fin n) × (Fin l → Fin n) // IsCopy H A rc.1 rc.2}

/-- Restricting a copy to the old rows and to the first `l` columns gives a copy of `H` in `A`. -/
theorem m3_restrict_isCopy {k l n q : ℕ} {H : BMat k l} (hH : NoZeroLine H) {A : BMat n n}
    (x : m3CopySet H A q) :
    IsCopy H A (fun i => ⟨(x.val.1 i).val, m3_row_old hH x.property i⟩)
      (fun j => ⟨(x.val.2 (Fin.castAdd q j)).val, m3_col_old hH x.property j⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i i' hii'
    exact x.property.1 hii'
  · intro j j' hjj'
    exact x.property.2.1 (DirectSumAux.castAdd_lt_castAdd_iff.mpr hjj')
  · intro i j
    dsimp only
    have h1 := DirectSumAux.blockDiag_apply_old_old A (zeros (q * n) (q * n))
      (m3_row_old hH x.property i) (m3_col_old hH x.property j)
    rw [← h1, x.property.2.2 i (Fin.castAdd q j), DirectSumAux.appendZeroCols_castAdd]

/-- **The restriction map.**  A copy of `[H 0^{k×q}]` in `[A 0; 0 0]` yields the copy of `H` in
`A` that it induces, together with the positions of the `q` appended columns. -/
noncomputable def m3CopySplit {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ)
    (A : BMat n n) (x : m3CopySet H A q) :
    m3HCopySet H A × (Fin q → Fin (n + q * n)) :=
  (⟨(fun i => ⟨(x.val.1 i).val, m3_row_old hH x.property i⟩,
    fun j => ⟨(x.val.2 (Fin.castAdd q j)).val, m3_col_old hH x.property j⟩),
    m3_restrict_isCopy hH x⟩,
   fun j => x.val.2 (Fin.natAdd l j))

/-- The restriction map is injective: the row map is recovered from the copy of `H` alone, and
the column map from that copy together with the positions of the appended columns. -/
theorem m3CopySplit_injective {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ)
    (A : BMat n n) : Function.Injective (m3CopySplit H hH q A) := by
  rintro ⟨⟨r, c⟩, hrc⟩ ⟨⟨r', c'⟩, hrc'⟩ hxy
  have hrowval : ∀ i : Fin k, (r i).val = (r' i).val := by
    intro i
    have h := congrArg
      (fun z : m3HCopySet H A × (Fin q → Fin (n + q * n)) => ((z.1).val.1 i).val) hxy
    simpa only [m3CopySplit, Fin.val_mk] using h
  have hcolval : ∀ j : Fin l, (c (Fin.castAdd q j)).val = (c' (Fin.castAdd q j)).val := by
    intro j
    have h := congrArg
      (fun z : m3HCopySet H A × (Fin q → Fin (n + q * n)) => ((z.1).val.2 j).val) hxy
    simpa only [m3CopySplit, Fin.val_mk] using h
  have htail : ∀ j : Fin q, c (Fin.natAdd l j) = c' (Fin.natAdd l j) := by
    intro j
    have h := congrArg
      (fun z : m3HCopySet H A × (Fin q → Fin (n + q * n)) => z.2 j) hxy
    simpa only [m3CopySplit] using h
  refine Subtype.ext (Prod.ext ?_ ?_)
  · funext i
    exact Fin.ext (hrowval i)
  · funext z
    rcases DirectSumAux.eq_castAdd_or_natAdd z with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Fin.ext (hcolval j)
    · exact htail j

theorem copyCount_appendZeroCols {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ)
    (A : BMat n n) :
    copyCount (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) ≤
      (n + q * n) ^ q * copyCount H A := by
  classical
  have hCS : Fintype.card (m3CopySet H A q)
      = copyCount (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) := by
    rw [copyCount, Fintype.card_subtype]
  have hHC : Fintype.card (m3HCopySet H A) = copyCount H A := by
    rw [copyCount, Fintype.card_subtype]
  have hinj := Fintype.card_le_of_injective (m3CopySplit H hH q A)
    (m3CopySplit_injective H hH q A)
  simp only [Fintype.card_prod, hHC, Fintype.card_fun, Fintype.card_fin] at hinj
  rw [hCS] at hinj
  calc copyCount (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n)))
      ≤ copyCount H A * (n + q * n) ^ q := hinj
    _ = (n + q * n) ^ q * copyCount H A := Nat.mul_comm _ _

end AppendZeroColsCount

/-! ## 5. Stage 3: general Z -/

/-- Paper's Theorem (direct sums), distance. -/
theorem editDist_blockDiag {k l p q n : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hk : 0 < k) (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) (A : BMat n n) :
    editDist (blockDiag H Z) (blockDiag A (blowup Z n)) = editDist H A := by
  exact DirectSumAux.editDist_blockDiag_eq H hH hk Z hp hq hZ A

abbrev m8CopySet (H : BMat k l) (Z : BMat p q) (A : BMat n n) : Type :=
  {rc : (Fin (k + p) → Fin (n + p * q * n)) × (Fin (l + q) → Fin (n + p * q * n)) //
    IsCopy (blockDiag H Z) (blockDiag A (blowup Z n)) rc.1 rc.2}

/-- The copies of `H` inside `A`, as a type. -/
abbrev m8HCopySet (H : BMat k l) (A : BMat n n) : Type :=
  {rc : (Fin k → Fin n) × (Fin l → Fin n) // IsCopy H A rc.1 rc.2}

/-- **Step 1 as a map.**  A copy of `blockDiag H Z` in `blockDiag A (blowup Z n)` splits into the
copy of `H` in `A` that it induces (all `H`-rows and `H`-columns of the copy are old, that is
`< n`, by `DirectSumAux.step1_old`) together with the two remaining strictly increasing index
maps `Fin p → Fin (n + p·q·n)` and `Fin q → Fin (n + p·q·n)`. -/
noncomputable def m8CopySplit (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n)
    (x : m8CopySet H Z A) :
    m8HCopySet H A × ((Fin p → Fin (n + p * q * n)) × (Fin q → Fin (n + p * q * n))) :=
  (⟨⟨fun i => ⟨(x.val.1 (Fin.castAdd p i)).val,
        (DirectSumAux.step1_old H Z hH hk hp hq hZ A x.property.1 x.property.2.1
          x.property.2.2).1 i⟩,
      fun j => ⟨(x.val.2 (Fin.castAdd q j)).val,
        (DirectSumAux.step1_old H Z hH hk hp hq hZ A x.property.1 x.property.2.1
          x.property.2.2).2 j⟩⟩,
    DirectSumAux.restrict_isCopy H Z A x.property.1 x.property.2.1 x.property.2.2
      (DirectSumAux.step1_old H Z hH hk hp hq hZ A x.property.1 x.property.2.1
        x.property.2.2).1
      (DirectSumAux.step1_old H Z hH hk hp hq hZ A x.property.1 x.property.2.1
        x.property.2.2).2⟩,
   (fun i => x.val.1 (Fin.natAdd k i), fun j => x.val.2 (Fin.natAdd l j)))

/-- The `H`-rows of the split copy, read off the old part. -/
theorem m8CopySplit_row (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n)
    (x : m8CopySet H Z A) (i : Fin k) :
    (((m8CopySplit H hH hk Z hp hq hZ A x).1).val.1 i).val
      = (x.val.1 (Fin.castAdd p i)).val := rfl

/-- The `H`-columns of the split copy, read off the old part. -/
theorem m8CopySplit_col (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n)
    (x : m8CopySet H Z A) (j : Fin l) :
    (((m8CopySplit H hH hk Z hp hq hZ A x).1).val.2 j).val
      = (x.val.2 (Fin.castAdd q j)).val := rfl

/-- The new rows of the split copy. -/
theorem m8CopySplit_newRow (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n)
    (x : m8CopySet H Z A) (i : Fin p) :
    (m8CopySplit H hH hk Z hp hq hZ A x).2.1 i = x.val.1 (Fin.natAdd k i) := rfl

/-- The new columns of the split copy. -/
theorem m8CopySplit_newCol (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n)
    (x : m8CopySet H Z A) (j : Fin q) :
    (m8CopySplit H hH hk Z hp hq hZ A x).2.2 j = x.val.2 (Fin.natAdd l j) := rfl

/-- **The split is injective.**  A strictly increasing map out of `Fin (k + p)` is determined by
its two halves, so the copy of `blockDiag H Z` is recovered from its `H`-part and its new
rows/columns. -/
theorem m8CopySplit_injective (H : BMat k l) (hH : NoZeroLine H) (hk : 0 < k)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective fun j i => Z i j) (A : BMat n n) :
    Function.Injective (m8CopySplit H hH hk Z hp hq hZ A) := by
  rintro ⟨⟨r, c⟩, hrc⟩ ⟨⟨r', c'⟩, hrc'⟩ hxy
  have hrowval : ∀ i : Fin k, (r (Fin.castAdd p i)).val = (r' (Fin.castAdd p i)).val := by
    intro i
    have h := congrArg
      (fun z : m8HCopySet H A × ((Fin p → Fin (n + p * q * n)) ×
          (Fin q → Fin (n + p * q * n))) => (((z.1).val.1) i).val) hxy
    rw [m8CopySplit_row, m8CopySplit_row] at h
    exact h
  have hcolval : ∀ j : Fin l, (c (Fin.castAdd q j)).val = (c' (Fin.castAdd q j)).val := by
    intro j
    have h := congrArg
      (fun z : m8HCopySet H A × ((Fin p → Fin (n + p * q * n)) ×
          (Fin q → Fin (n + p * q * n))) => (((z.1).val.2) j).val) hxy
    rw [m8CopySplit_col, m8CopySplit_col] at h
    exact h
  have hnewrow : ∀ i : Fin p, r (Fin.natAdd k i) = r' (Fin.natAdd k i) := by
    intro i
    have h := congrArg
      (fun z : m8HCopySet H A × ((Fin p → Fin (n + p * q * n)) ×
          (Fin q → Fin (n + p * q * n))) => (z.2).1 i) hxy
    rw [m8CopySplit_newRow, m8CopySplit_newRow] at h
    exact h
  have hnewcol : ∀ j : Fin q, c (Fin.natAdd l j) = c' (Fin.natAdd l j) := by
    intro j
    have h := congrArg
      (fun z : m8HCopySet H A × ((Fin p → Fin (n + p * q * n)) ×
          (Fin q → Fin (n + p * q * n))) => (z.2).2 j) hxy
    rw [m8CopySplit_newCol, m8CopySplit_newCol] at h
    exact h
  have hreq : r = r' := by
    funext z
    rcases DirectSumAux.eq_castAdd_or_natAdd z with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Fin.ext (hrowval i)
    · exact hnewrow i
  have hceq : c = c' := by
    funext z
    rcases DirectSumAux.eq_castAdd_or_natAdd z with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Fin.ext (hcolval i)
    · exact hnewcol i
  exact Subtype.ext (Prod.ext hreq hceq)

/-- The empty pattern has exactly one copy in every square host. -/
theorem m8copyCount_empty {n : ℕ} (H : BMat 0 0) (A : BMat n n) : copyCount H A = 1 := by
  have hfilter : (Finset.univ.filter (fun rc : (Fin 0 → Fin n) × (Fin 0 → Fin n) =>
      IsCopy H A rc.1 rc.2)) = Finset.univ := by
    refine Finset.filter_true_of_mem (fun x _ => ?_)
    exact ⟨fun a _ _ => a.elim0, fun a _ _ => a.elim0, fun i => i.elim0⟩
  rw [copyCount, hfilter, Finset.card_univ]
  simp

/-- **The empty pattern is polynomially removable**, trivially: `copyCount` of it is `1`, so
`c = C = 1` works because `ε ≤ 1`.  This is the missing `0 < k` case of §6. -/
theorem m8polyRemoval_empty (H : BMat 0 0) : PolyRemoval H := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro n A ε hε0 hε1 hdist
  rw [m8copyCount_empty H A]
  have hmain : (1 : ℝ) * ε ^ (1 : ℝ) * (n : ℝ) ^ (0 + 0) = ε := by
    rw [Real.rpow_one, pow_zero, mul_one, one_mul]
  rw [hmain]
  simpa using hε1

/-- **`NoZeroLine` and one empty dimension force both to be empty.**  Hence the `k = 0`
(or `l = 0`) case of every statement lacking an `hk : 0 < k` hypothesis is the case
`H = empty`, which `m8polyRemoval_empty` settles. -/
theorem m8eq_zero_of_noZeroLine {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (h : k = 0 ∨ l = 0) : k = 0 ∧ l = 0 := by
  rcases h with hk | hl
  · subst hk
    refine ⟨rfl, ?_⟩
    by_contra hl
    obtain ⟨i, -⟩ := hH.2 ⟨0, Nat.pos_of_ne_zero hl⟩
    exact Fin.elim0 i
  · subst hl
    refine ⟨?_, rfl⟩
    by_contra hk
    obtain ⟨j, -⟩ := hH.1 ⟨0, Nat.pos_of_ne_zero hk⟩
    exact Fin.elim0 j

/-- Paper's Theorem (direct sums), count. -/
theorem copyCount_blockDiag {k l p q n : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) (A : BMat n n) :
    copyCount (blockDiag H Z) (blockDiag A (blowup Z n)) ≤
      (n + p * q * n) ^ (p + q) * copyCount H A := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `hH` forces `l = 0`, and then the crude bound is an equality
    subst hk0
    have hl0 : l = 0 := by
      by_contra hl
      obtain ⟨i, -⟩ := hH.2 ⟨0, Nat.pos_of_ne_zero hl⟩
      exact Fin.elim0 i
    subst hl0
    have hcount : copyCount (H : BMat 0 0) A = 1 := m8copyCount_empty H A
    rw [hcount, mul_one]
    have h1 := DirectSumAux.copyCount_le (blockDiag H Z) (blockDiag A (blowup Z n))
    simpa [Nat.zero_add, pow_add] using h1
  · -- main case `0 < k`
    have hCS : Fintype.card (m8CopySet H Z A)
        = copyCount (blockDiag H Z) (blockDiag A (blowup Z n)) := by
      rw [copyCount, Fintype.card_subtype]
    have hHC : Fintype.card (m8HCopySet H A) = copyCount H A := by
      rw [copyCount, Fintype.card_subtype]
    have hinj := Fintype.card_le_of_injective (m8CopySplit H hH hk Z hp hq hZ A)
      (m8CopySplit_injective H hH hk Z hp hq hZ A)
    simp only [Fintype.card_prod, hHC, Fintype.card_fun, Fintype.card_fin] at hinj
    rw [hCS, ← pow_add] at hinj
    calc copyCount (blockDiag H Z) (blockDiag A (blowup Z n))
        ≤ copyCount H A * (n + p * q * n) ^ (p + q) := hinj
      _ = (n + p * q * n) ^ (p + q) * copyCount H A := Nat.mul_comm _ _

/-- **§3's `copyCount_blockDiag_one`** (identical statement to the one in `Statements.lean`),
derived from the general bound: `ones 1 1` is a `1 × 1` matrix with distinct rows and distinct
columns, and `blowup (ones 1 1) n = ones n n`. -/
theorem m8copyCount_blockDiag_one {k l n : ℕ} (H : BMat k l) (hH : NoZeroLine H) (A : BMat n n) :
    copyCount (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) ≤
      (n + n) ^ 2 * copyCount H A := by
  have h := copyCount_blockDiag (n := n) H hH (ones 1 1) (by omega) (by omega)
    (Or.inl (fun i j _ => Subsingleton.elim i j)) A
  rw [DirectSumAux.blowup_ones_eq] at h
  rw [show 1 * 1 * n = n from by omega] at h
  exact h

/-! ## 6. Stage 4: the corollary -/

/-- Paper's Corollary: attaching `Z` to a counterexample gives a counterexample. -/
theorem not_polyRemoval_blockDiag {k l p q : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j))
    (hcounter : ¬ PolyRemoval H) :
    ¬ PolyRemoval (blockDiag H Z) := by
  intro hpoly
  have hk : 0 < k := by
    by_contra hkn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkn
    obtain ⟨hk0, hl0⟩ := m8eq_zero_of_noZeroLine H hH (Or.inl hk0)
    subst k
    subst l
    exact hcounter (m8polyRemoval_empty H)
  rcases hpoly with ⟨c, C, hc, hC, hpoly⟩
  apply hcounter
  let s : ℝ := 1 + (p * q : ℕ)
  have hs0 : 0 < s := by
    dsimp [s]
    positivity
  have hs1 : 1 ≤ s := by
    have hpq : (0 : ℝ) ≤ (p * q : ℕ) := by positivity
    dsimp [s]
    linarith
  refine ⟨c / s ^ (2 * C), C, div_pos hc (Real.rpow_pos_of_pos hs0 _), hC, ?_⟩
  intro n A ε hε0 hε1 hdist
  by_cases hn : 0 < n
  · let m : ℕ := n + p * q * n
    have hm : (m : ℝ) = s * (n : ℝ) := by
      simp only [m, s, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    have hm0 : 0 < (m : ℝ) := by rw [hm]; positivity
    have hnm : (n : ℝ) ≤ (m : ℝ) := by
      rw [hm]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    have hεs0 : 0 < ε / s ^ 2 := div_pos hε0 (pow_pos hs0 2)
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have hεs1 : ε / s ^ 2 ≤ 1 :=
      (div_le_one (pow_pos hs0 2)).2 (hε1.trans hs2)
    have hdist' : ε / s ^ 2 * (m : ℝ) ^ 2 ≤
        (editDist (blockDiag H Z) (blockDiag A (blowup Z n)) : ℝ) := by
      rw [editDist_blockDiag H hH hk Z hp hq hZ A]
      calc
        ε / s ^ 2 * (m : ℝ) ^ 2 = ε * (n : ℝ) ^ 2 := by
          rw [hm]
          field_simp [ne_of_gt hs0]
          <;> ring
        _ ≤ (editDist H A : ℝ) := hdist
    have hmain := hpoly m (blockDiag A (blowup Z n)) (ε / s ^ 2)
      hεs0 hεs1 hdist'
    have hcount : (copyCount (blockDiag H Z) (blockDiag A (blowup Z n)) : ℝ) ≤
        (m : ℝ) ^ (p + q) * (copyCount H A : ℝ) := by
      exact_mod_cast copyCount_blockDiag H hH Z hp hq hZ A
    have hmul :
        (c * (ε / s ^ 2) ^ C * (m : ℝ) ^ (k + l)) * (m : ℝ) ^ (p + q) ≤
          (copyCount H A : ℝ) * (m : ℝ) ^ (p + q) := by
      have he : (k + p) + (l + q) = (k + l) + (p + q) := by omega
      calc
        (c * (ε / s ^ 2) ^ C * (m : ℝ) ^ (k + l)) * (m : ℝ) ^ (p + q) =
            c * (ε / s ^ 2) ^ C * (m : ℝ) ^ ((k + p) + (l + q)) := by
          rw [he, pow_add]
          ring
        _ ≤ (copyCount (blockDiag H Z) (blockDiag A (blowup Z n)) : ℝ) := hmain
        _ ≤ (m : ℝ) ^ (p + q) * (copyCount H A : ℝ) := hcount
        _ = (copyCount H A : ℝ) * (m : ℝ) ^ (p + q) := by ring
    have hcancel : c * (ε / s ^ 2) ^ C * (m : ℝ) ^ (k + l) ≤
        (copyCount H A : ℝ) :=
      (mul_le_mul_iff_left₀ (pow_pos hm0 (p + q))).mp hmul
    have hpow : (s ^ 2) ^ C = s ^ (2 * C) := by
      calc
        (s ^ 2) ^ C = (s ^ (2 : ℝ)) ^ C := by rw [Real.rpow_two]
        _ = s ^ (2 * C) := (Real.rpow_mul (le_of_lt hs0) 2 C).symm
    have hconst : c / s ^ (2 * C) * ε ^ C = c * (ε / s ^ 2) ^ C := by
      rw [Real.div_rpow (le_of_lt hε0) (sq_nonneg s), hpow]
      ring
    calc
      c / s ^ (2 * C) * ε ^ C * (n : ℝ) ^ (k + l) =
          c * (ε / s ^ 2) ^ C * (n : ℝ) ^ (k + l) := by rw [hconst]
      _ ≤ c * (ε / s ^ 2) ^ C * (m : ℝ) ^ (k + l) := by
        have hpow_le : (n : ℝ) ^ (k + l) ≤ (m : ℝ) ^ (k + l) :=
          pow_le_pow_left₀ (by positivity) hnm (k + l)
        have hnonneg : 0 ≤ c * (ε / s ^ 2) ^ C :=
          mul_nonneg (le_of_lt hc) (Real.rpow_nonneg (by positivity) C)
        exact mul_le_mul_of_nonneg_left hpow_le hnonneg
      _ ≤ (copyCount H A : ℝ) := hcancel
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [Nat.cast_zero, zero_pow (by omega : k + l ≠ 0), mul_zero]
    exact Nat.cast_nonneg _


/-! ### The negation shape of `PolyRemoval` -/

/-- `¬ PolyRemoval H` unpacked: for every putative `c, C > 0` there is a host witnessing the
failure, with the *strict* inequality `N_H(A) < c ε^C n^(a+b)`. -/
lemma m4not_polyRemoval_iff {a b : ℕ} (H : BMat a b) :
    ¬ PolyRemoval H ↔
      ∀ c C : ℝ, 0 < c → 0 < C → ∃ (n : ℕ) (A : BMat n n) (ε : ℝ),
        0 < ε ∧ ε ≤ 1 ∧ ε * (n : ℝ) ^ 2 ≤ (editDist H A : ℝ) ∧
          (copyCount H A : ℝ) < c * ε ^ C * (n : ℝ) ^ (a + b) := by
  unfold PolyRemoval
  constructor
  · intro h c C hc hC
    by_contra hcon
    refine h ⟨c, C, hc, hC, fun n A ε h1 h2 h3 => ?_⟩
    by_contra hbad
    exact hcon ⟨n, A, ε, h1, h2, h3, not_le.mp hbad⟩
  · rintro h ⟨c, C, hc, hC, hP⟩
    obtain ⟨n, A, ε, h1, h2, h3, h4⟩ := h c C hc hC
    exact absurd (hP n A ε h1 h2 h3) (not_le.mpr h4)

/-! ### The `0 × 0` pattern has polynomial removal

Only used to see that a counterexample has `0 < a + b`, so that a counterexample host has positive
size `n` and `(n : ℝ) ^ (a + b)` can be cancelled (`≠ 0`). -/

lemma m4copyCount_zero_zero {n : ℕ} (A : BMat n n) : copyCount (H : BMat 0 0) A = 1 := by
  classical
  have h1 : (Finset.univ.filter
      (fun rc : (Fin 0 → Fin n) × (Fin 0 → Fin n) => IsCopy H A rc.1 rc.2)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    rintro ⟨r, c⟩ -
    exact ⟨fun a _ _ => a.elim0, fun a _ _ => a.elim0, fun i => i.elim0⟩
  rw [copyCount, h1, Finset.card_univ, Fintype.card_prod, Fintype.card_fun]
  simp

lemma m4polyRemoval_zero_zero (H : BMat 0 0) : PolyRemoval H := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro n A ε hε hε1 _
  rw [m4copyCount_zero_zero A, Nat.cast_one, Real.rpow_one]
  have h0 : (n : ℝ) ^ (0 + 0) = 1 := by simp
  rw [h0, mul_one]
  simpa using hε1

/-- A counterexample pattern is never of shape `0 × 0`. -/
lemma m4pos_add_of_not_polyRemoval {a b : ℕ} (H : BMat a b) (h : ¬ PolyRemoval H) :
    0 < a + b := by
  rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
  · exfalso
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha
    subst hb
    exact h (m4polyRemoval_zero_zero H)
  · exact hpos

/-! ### The real-arithmetic core

With `m = s·n`, `ε' = ε/s²` and `c = c'·s^(A-2C')`, one has
`m^E · (c·ε^C'·n^A) = c'·ε'^C'·m^(A+E)`.  This is exactly the paper's line
`c ε^C n^(k+l) m^(p+q) = c' ε'^C' m^((k+p)+(l+q))`. -/

lemma m4key_identity {s ε c' n A E C' : ℝ} (hs : 0 < s) (hε : 0 < ε) (hn : 0 < n) :
    (s * n) ^ E * (c' * s ^ (A - 2 * C') * ε ^ C' * n ^ A) =
      c' * (ε / s ^ 2) ^ C' * (s * n) ^ (A + E) := by
  -- `rpow` additivity, in the four shapes the identity needs
  have h1 : s ^ E * s ^ (A - 2 * C') = s ^ (A + E - 2 * C') := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have h2 : n ^ E * n ^ A = n ^ (A + E) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have h3 : s ^ (-(2 * C')) * s ^ (A + E) = s ^ (A + E - 2 * C') := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have h4 : s ^ (-(2 * C')) = ((s ^ 2) ^ C')⁻¹ := by
    have h5 : (s ^ 2) ^ C' = s ^ (2 * C') := by
      rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm, Real.rpow_mul (le_of_lt hs)]
    rw [h5]
    exact Real.rpow_neg (le_of_lt hs) (2 * C')
  have hdiv : (ε / s ^ 2) ^ C' = ε ^ C' * s ^ (-(2 * C')) := by
    rw [Real.div_rpow (le_of_lt hε) (by positivity : (0 : ℝ) ≤ s ^ 2) C', h4, div_eq_mul_inv]
  have hsE : (s * n) ^ E = s ^ E * n ^ E := Real.mul_rpow (le_of_lt hs) (le_of_lt hn)
  have hsAE : (s * n) ^ (A + E) = s ^ (A + E) * n ^ (A + E) :=
    Real.mul_rpow (le_of_lt hs) (le_of_lt hn)
  rw [hsE, hsAE, hdiv]
  calc (s ^ E * n ^ E) * (c' * s ^ (A - 2 * C') * ε ^ C' * n ^ A)
      = c' * ε ^ C' * (s ^ E * s ^ (A - 2 * C')) * (n ^ E * n ^ A) := by ring
    _ = c' * ε ^ C' * s ^ (A + E - 2 * C') * n ^ (A + E) := by rw [h1, h2]
    _ = c' * (ε ^ C' * s ^ (-(2 * C'))) * (s ^ (A + E) * n ^ (A + E)) := by
        rw [← h3]
        ring

/-! ### The abstract transfer lemma -/

/-- If a construction `H ↦ H'` grows hosts as `M n = s·n` (`1 ≤ s`), preserves the edit distance,
multiplies the copy count by at most `(M n)^e`, and increases rows+columns by exactly `e`, then a
counterexample `H` gives a counterexample `H'`.

This is the paper's §6 Corollary argument, with the host chosen as `A⁺` and
`ε' = ε/s²`, `c' = c·s^(2C' - (a+b))`. -/
theorem m4not_polyRemoval_of_transfer
    {a b a' b' : ℕ} (H : BMat a b) (H' : BMat a' b')
    (s : ℝ) (hs : 1 ≤ s) (e : ℕ) (M : ℕ → ℕ)
    (hM : ∀ n : ℕ, (M n : ℝ) = s * (n : ℝ))
    (hab : a' + b' = a + b + e)
    (Md : (n : ℕ) → BMat n n → BMat (M n) (M n))
    (hD : ∀ (n : ℕ) (A : BMat n n), editDist H' (Md n A) = editDist H A)
    (hN : ∀ (n : ℕ) (A : BMat n n), copyCount H' (Md n A) ≤ M n ^ e * copyCount H A)
    (hc : ¬ PolyRemoval H) : ¬ PolyRemoval H' := by
  have hab0 : 0 < a + b := m4pos_add_of_not_polyRemoval H hc
  rw [m4not_polyRemoval_iff] at hc ⊢
  intro c' C' hc' hC'
  have hs0 : 0 < s := by linarith
  have hsq : (0 : ℝ) < s ^ 2 := by positivity
  set c : ℝ := c' * s ^ (((a + b : ℕ) : ℝ) - 2 * C') with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact mul_pos hc' (Real.rpow_pos_of_pos hs0 _)
  obtain ⟨n, A, ε, hε, hε1, hdist, hcnt⟩ := hc c C' hcpos hC'
  -- a counterexample host has positive size
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have hn0 : (n : ℝ) = 0 := by rw [h0, Nat.cast_zero]
      rw [hn0, zero_pow (by omega : a + b ≠ 0), mul_zero] at hcnt
      have hnn := Nat.cast_nonneg (α := ℝ) (copyCount H A)
      linarith
    · exact hpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (M n : ℝ) := by rw [hM n]; positivity
  refine ⟨M n, Md n A, ε / s ^ 2, ?_, ?_, ?_, ?_⟩
  · exact div_pos hε hsq
  · rw [div_le_one hsq]
    nlinarith
  · -- the distance is unchanged, and `ε'·(s n)^2 = ε·n^2`
    rw [hD n A, hM n]
    have hEq : ε / s ^ 2 * (s * (n : ℝ)) ^ 2 = ε * (n : ℝ) ^ 2 := by
      have hne : (s : ℝ) ^ 2 ≠ 0 := ne_of_gt hsq
      rw [mul_pow]
      calc ε / s ^ 2 * (s ^ 2 * (n : ℝ) ^ 2) = ε / s ^ 2 * s ^ 2 * (n : ℝ) ^ 2 := by ring
        _ = ε * (n : ℝ) ^ 2 := by rw [div_mul_cancel₀ ε hne]
    rw [hEq]
    exact hdist
  · -- the count: multiply the failure of `H` by `(M n)^e` and rescale
    have hub : (copyCount H' (Md n A) : ℝ) ≤ (M n : ℝ) ^ e * (copyCount H A : ℝ) := by
      have := hN n A
      exact_mod_cast this
    have hlt : (M n : ℝ) ^ e * (copyCount H A : ℝ) <
        (M n : ℝ) ^ e * (c * ε ^ C' * (n : ℝ) ^ (a + b)) :=
      mul_lt_mul_of_pos_left hcnt (pow_pos hmR e)
    have habR : ((a' + b' : ℕ) : ℝ) = ((a + b : ℕ) : ℝ) + (e : ℝ) := by
      rw [hab]
      push_cast
      ring
    have key : (M n : ℝ) ^ e * (c * ε ^ C' * (n : ℝ) ^ (a + b))
        = c' * (ε / s ^ 2) ^ C' * (M n : ℝ) ^ (a' + b') := by
      rw [← Real.rpow_natCast (M n) e, ← Real.rpow_natCast (n : ℝ) (a + b),
        ← Real.rpow_natCast (M n) (a' + b'), hM n, hcdef, habR]
      exact m4key_identity hs0 hε hnR
    linarith

/-! ### Sanity check: the transfer lemma reproduces the general direct-sum corollary -/

/-- The direct-sum corollary of §6, re-derived through `m4not_polyRemoval_of_transfer` from the two
(already proved) §5 theorems.  Consistency check for the transfer lemma. -/
theorem m4not_polyRemoval_blockDiag_via_transfer {k l p q : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)
    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j))
    (hcounter : ¬ PolyRemoval H) : ¬ PolyRemoval (blockDiag H Z) := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hk : 0 < k := by
    by_contra hkn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkn
    obtain ⟨hk0, hl0⟩ : k = 0 ∧ l = 0 := by
      subst hk0
      refine ⟨rfl, ?_⟩
      by_contra hl
      obtain ⟨i, -⟩ := hH.2 ⟨0, Nat.pos_of_ne_zero hl⟩
      exact Fin.elim0 i
    subst hk0
    subst hl0
    exact hcounter (m4polyRemoval_zero_zero H)
  refine m4not_polyRemoval_of_transfer H (blockDiag H Z) (1 + (p : ℝ) * (q : ℝ)) ?_ (p + q)
    (fun n => n + p * q * n) ?_ ?_ (fun n A => blockDiag A (blowup Z n)) ?_ ?_ hcounter
  · nlinarith
  · intro n
    push_cast
    ring
  · omega
  · intro n A
    exact DirectSumAux.editDist_blockDiag_eq H hH hk Z hp hq hZ A
  · intro n A
    exact copyCount_blockDiag H hH Z hp hq hZ A

/-! ### The zero-column variant -/

/-- **§4, derived from the two per-host lemmas.**  This is the proof of
`not_polyRemoval_appendZeroCols` once `editDist_appendZeroCols` and `copyCount_appendZeroCols`
are available: `A⁺ = blockDiag A (zeros (q·n) (q·n))` has size `(1+q)·n`, and the count picks up
the factor `((1+q)n)^q`, while `H' = appendZeroCols H q` has `k + (l+q) = (k+l) + q` rows and
columns. -/
theorem m4not_polyRemoval_appendZeroCols_of
    {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ) (hq : 0 < q)
    (hD : ∀ (n : ℕ) (A : BMat n n),
      editDist (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) = editDist H A)
    (hN : ∀ (n : ℕ) (A : BMat n n),
      copyCount (appendZeroCols H q) (blockDiag A (zeros (q * n) (q * n))) ≤
        (n + q * n) ^ q * copyCount H A)
    (hcounter : ¬ PolyRemoval H) : ¬ PolyRemoval (appendZeroCols H q) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  refine m4not_polyRemoval_of_transfer H (appendZeroCols H q) (1 + (q : ℝ)) ?_ q
    (fun n => n + q * n) ?_ ?_ (fun n A => blockDiag A (zeros (q * n) (q * n))) hD hN hcounter
  · linarith
  · intro n
    push_cast
    ring
  · omega


/-- The Variant's corollary. -/
theorem not_polyRemoval_appendZeroCols {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H) (q : ℕ)
    (hq : 0 < q) (hcounter : ¬ PolyRemoval H) :
    ¬ PolyRemoval (appendZeroCols H q) := by
  exact m4not_polyRemoval_appendZeroCols_of H hH q hq
    (fun n A => editDist_appendZeroCols H hH q A)
    (fun n A => copyCount_appendZeroCols H hH q A) hcounter

end OrderedRemoval


#print axioms OrderedRemoval.editDist_eq_zero_iff
#print axioms OrderedRemoval.editDist_blockDiag_one
#print axioms OrderedRemoval.editDist_blockDiag


#print axioms OrderedRemoval.copyCount_blockDiag
#print axioms OrderedRemoval.not_polyRemoval_blockDiag
/-! ## 7. An explicit infinite family of counterexamples: iterated padding with `(1)` -/

namespace OrderedRemoval

/-! ### The dependent family `padding H t`

`padding H t` is `H` with `t` copies of the `1 × 1` block `(1)` attached on the diagonal, one at a
time: step `t` adjoins one new row and one new column with a single `1` in the corner.  It is the
`(k+t) × (l+t)` pattern `[H 0 … 0; 0 1 0 …; …; 0 … 0 1]`, and it is the pattern of the direct-sum
theorem `editDist_blockDiag` / `not_polyRemoval_blockDiag` at every step, with `Z = (1)`. -/

/-- `padding H t`: `H` with `t` successive `(1)`-blocks attached diagonally; a `(k+t) × (l+t)`
pattern. -/
def padding {k l : ℕ} (H : BMat k l) : (t : ℕ) → BMat (k + t) (l + t)
  | 0 => H
  | t + 1 =>
    -- the `show` fixes the size of the recursive call: `k + (t+1)` is definitionally `(k+t) + 1`
    show BMat ((k + t) + 1) ((l + t) + 1) from blockDiag (padding H t) (ones 1 1)

/-- `padding H 0 = H`: the family starts at `H`. -/
theorem padding_zero {k l : ℕ} (H : BMat k l) : padding H 0 = H := rfl

/-- One padding step: `padding H (t+1) = [padding H t 0; 0 1]`. -/
theorem padding_succ {k l : ℕ} (H : BMat k l) (t : ℕ) :
    padding H (t + 1) = blockDiag (padding H t) (ones 1 1) := rfl

/-- The first member of the family, spelled out: `padding H 1 = [H 0; 0 1]`. -/
theorem padding_one {k l : ℕ} (H : BMat k l) :
    padding H 1 = blockDiag H (ones 1 1) := rfl

/-! ### No zero line -/

/-- `(1)` has no zero line. -/
theorem noZeroLine_ones_one_one : NoZeroLine (ones 1 1) :=
  ⟨fun _ => ⟨0, rfl⟩, fun _ => ⟨0, rfl⟩⟩

/-- A block diagonal `[H 0; 0 Z]` has no zero line if `H` and `Z` have none. -/
theorem noZeroLine_blockDiag {k l p q : ℕ} {H : BMat k l} {Z : BMat p q}
    (hH : NoZeroLine H) (hZ : NoZeroLine Z) : NoZeroLine (blockDiag H Z) := by
  obtain ⟨hHrow, hHcol⟩ := hH
  obtain ⟨hZrow, hZcol⟩ := hZ
  constructor
  · intro i
    rcases DirectSumAux.eq_castAdd_or_natAdd i with ⟨i', rfl⟩ | ⟨i', rfl⟩
    · obtain ⟨j', hj'⟩ := hHrow i'
      exact ⟨Fin.castAdd q j', by rw [DirectSumAux.blockDiag_castAdd_castAdd, hj']⟩
    · obtain ⟨j', hj'⟩ := hZrow i'
      exact ⟨Fin.natAdd l j', by rw [DirectSumAux.blockDiag_natAdd_natAdd, hj']⟩
  · intro j
    rcases DirectSumAux.eq_castAdd_or_natAdd j with ⟨j', rfl⟩ | ⟨j', rfl⟩
    · obtain ⟨i', hi'⟩ := hHcol j'
      exact ⟨Fin.castAdd p i', by rw [DirectSumAux.blockDiag_castAdd_castAdd, hi']⟩
    · obtain ⟨i', hi'⟩ := hZcol j'
      exact ⟨Fin.natAdd k i', by rw [DirectSumAux.blockDiag_natAdd_natAdd, hi']⟩

/-- Every member of the family has no zero line. -/
theorem padding_noZeroLine {k l : ℕ} {H : BMat k l} (hH : NoZeroLine H) (t : ℕ) :
    NoZeroLine (padding H t) := by
  induction t with
  | zero => exact hH
  | succ t ih => exact noZeroLine_blockDiag ih noZeroLine_ones_one_one

/-! ### Every member of the family is a counterexample -/

/-- One padding step preserves being a counterexample: this is `not_polyRemoval_blockDiag` for the
`1 × 1` block `Z = (1)` (so `p = q = 1`, and its single row is trivially injective).  It is the
only external ingredient of the family; the general result for arbitrary `Z` is
`not_polyRemoval_blockDiag`. -/
theorem padding_not_polyRemoval {k l : ℕ} {H : BMat k l} (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H)
    (hstep : ∀ {a b : ℕ} (X : BMat a b), NoZeroLine X → ¬ PolyRemoval X →
      ¬ PolyRemoval (blockDiag X (ones 1 1))) (t : ℕ) :
    ¬ PolyRemoval (padding H t) := by
  induction t with
  | zero => exact hcounter
  | succ t ih => exact hstep (padding H t) (padding_noZeroLine hH t) ih

/-- The same, derived from the general corollary `not_polyRemoval_blockDiag` (arbitrary `Z` with
`p, q ≥ 1` and pairwise distinct rows or columns). -/
theorem padding_not_polyRemoval_of_blockDiag {k l : ℕ} {H : BMat k l} (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H)
    (hmain : ∀ {a b p q : ℕ} (X : BMat a b), NoZeroLine X → (Z : BMat p q) → 0 < p → 0 < q →
      (Function.Injective Z ∨ Function.Injective fun j i => Z i j) → ¬ PolyRemoval X →
      ¬ PolyRemoval (blockDiag X Z)) (t : ℕ) :
    ¬ PolyRemoval (padding H t) :=
  padding_not_polyRemoval hH hcounter
    (fun X hX hc =>
      hmain X hX (ones 1 1) (by omega) (by omega)
        (Or.inl fun _ _ _ => Subsingleton.elim _ _) hc) t

/-! ### The family of patterns is injective, hence infinite -/

/-- A binary pattern of arbitrary rectangular size. -/
abbrev Pattern : Type := Σ d : ℕ × ℕ, BMat d.1 d.2

/-- `paddingFamily H` is the explicit sequence of patterns: step `t` is `padding H t`, tagged by
its size `(k+t, l+t)`. -/
def paddingFamily {k l : ℕ} (H : BMat k l) : ℕ → Pattern :=
  fun t => ⟨(k + t, l + t), padding H t⟩

/-- The size of the `t`-th member of the family is `(k+t, l+t)`. -/
theorem paddingFamily_size {k l : ℕ} (H : BMat k l) (t : ℕ) :
    (paddingFamily H t).1 = (k + t, l + t) := rfl

/-- The second component of the `t`-th member of the family is `padding H t`. -/
theorem paddingFamily_pattern {k l : ℕ} (H : BMat k l) (t : ℕ) :
    (paddingFamily H t).2 = padding H t := rfl

/-- **Injectivity.**  Distinct `t` give distinct patterns, because the size `(k+t, l+t)` of the
pattern determines `t`. -/
theorem paddingFamily_injective {k l : ℕ} (H : BMat k l) :
    Function.Injective (paddingFamily H) := by
  intro s t hst
  have hsize : (k + s, l + s) = (k + t, l + t) := congrArg Sigma.fst hst
  simp only [Prod.mk.injEq] at hsize
  omega

/-- Hence the family of patterns is infinite. -/
theorem paddingFamily_infinite {k l : ℕ} (H : BMat k l) :
    (Set.range (paddingFamily H)).Infinite :=
  Set.infinite_range_of_injective (paddingFamily_injective H)

/-- **The explicit infinite family of counterexamples.**  If `H` has no zero line and is a
counterexample to polynomial ordered removal, then the patterns `padding H t` (`t = 0, 1, 2, …`),
obtained by adjoining `t` diagonal `(1)`-blocks to `H`, are pairwise distinct `(k+t) × (l+t)`
patterns, each without zero line and each again a counterexample. -/
theorem padding_family_infinite_counterexamples {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H)
    (hstep : ∀ {a b : ℕ} (X : BMat a b), NoZeroLine X → ¬ PolyRemoval X →
      ¬ PolyRemoval (blockDiag X (ones 1 1))) :
    (Set.range (paddingFamily H)).Infinite ∧
      Function.Injective (paddingFamily H) ∧
      (∀ t : ℕ, NoZeroLine (padding H t) ∧ ¬ PolyRemoval (padding H t)) ∧
      (∀ t : ℕ, (paddingFamily H t).1 = (k + t, l + t)) :=
  ⟨paddingFamily_infinite H, paddingFamily_injective H,
    fun t => ⟨padding_noZeroLine hH t, padding_not_polyRemoval hH hcounter hstep t⟩,
    paddingFamily_size H⟩

/-- The same, phrased as the existence of an injective sequence of counterexamples. -/
theorem exists_infinite_counterexample_family {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H)
    (hstep : ∀ {a b : ℕ} (X : BMat a b), NoZeroLine X → ¬ PolyRemoval X →
      ¬ PolyRemoval (blockDiag X (ones 1 1))) :
    ∃ f : ℕ → Pattern, Function.Injective f ∧
      (∀ t : ℕ, (f t).1 = (k + t, l + t) ∧ NoZeroLine (f t).2 ∧ ¬ PolyRemoval (f t).2) :=
  ⟨paddingFamily H, paddingFamily_injective H,
    fun t => ⟨paddingFamily_size H t, padding_noZeroLine hH t,
      padding_not_polyRemoval hH hcounter hstep t⟩⟩

/-- Counterexamples of unbounded size: for every `N`, the member `padding H N` is a counterexample
with no zero line and at least `N` rows and at least `N` columns. -/
theorem exists_counterexample_size_ge {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H)
    (hstep : ∀ {a b : ℕ} (X : BMat a b), NoZeroLine X → ¬ PolyRemoval X →
      ¬ PolyRemoval (blockDiag X (ones 1 1))) (N : ℕ) :
    ∃ (a b : ℕ) (P : BMat a b), N ≤ a ∧ N ≤ b ∧ NoZeroLine P ∧ ¬ PolyRemoval P :=
  ⟨k + N, l + N, padding H N, by omega, by omega, padding_noZeroLine hH N,
    padding_not_polyRemoval hH hcounter hstep N⟩

end OrderedRemoval
/-! ## 8. The top-level theorem: an explicit infinite family of counterexamples -/

namespace OrderedRemoval

/-- One padding step preserves being a counterexample: this is `not_polyRemoval_blockDiag` at
`Z = (1)` (`p = q = 1`; a one-row matrix is trivially injective).  This is the only ingredient the
family needs beyond the general direct-sum corollary. -/
theorem padding_step {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H) (hcounter : ¬ PolyRemoval H) :
    ¬ PolyRemoval (blockDiag H (ones 1 1)) :=
  not_polyRemoval_blockDiag H hH (ones 1 1) (by omega) (by omega)
    (Or.inl (fun _ _ _ => Subsingleton.elim _ _)) hcounter

/-- Every member of the explicit family `padding H t` (`t = 0, 1, 2, …`) is a counterexample. -/
theorem padding_counterexample {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H) (t : ℕ) : ¬ PolyRemoval (padding H t) :=
  padding_not_polyRemoval hH hcounter (fun X hX hc => padding_step X hX hc) t

/-- **The main theorem: infinitely many counterexamples, explicitly.**

For every binary pattern `H` with no zero line that is a counterexample to polynomial ordered
removal, the sequence `t ↦ ⟨(k+t, l+t), padding H t⟩` (`t = 0, 1, 2, …`) is an injective sequence
of patterns: it adjoins `t` diagonal `(1)`-blocks to `H`, so its `t`-th member is a
`(k+t) × (l+t)` pattern, its size determines `t`, every member has no zero line, and every member
is again a counterexample.  Hence there are infinitely many counterexamples. -/
theorem infinite_family_of_counterexample {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H) :
    Function.Injective (paddingFamily H) ∧ (Set.range (paddingFamily H)).Infinite ∧
      (∀ t : ℕ, NoZeroLine (padding H t) ∧ ¬ PolyRemoval (padding H t)) ∧
      (∀ t : ℕ, (paddingFamily H t).1 = (k + t, l + t)) :=
  ⟨paddingFamily_injective H, paddingFamily_infinite H,
    fun t => ⟨padding_noZeroLine hH t, padding_counterexample H hH hcounter t⟩,
    paddingFamily_size H⟩

/-- The same as an injective sequence of patterns, each tagged by its size. -/
theorem exists_injective_counterexample_family {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H) :
    ∃ f : ℕ → Pattern, Function.Injective f ∧
      (∀ t : ℕ, (f t).1 = (k + t, l + t) ∧ NoZeroLine (f t).2 ∧ ¬ PolyRemoval (f t).2) :=
  exists_infinite_counterexample_family H hH hcounter (fun X hX hc => padding_step X hX hc)

/-- Counterexamples with no zero line of unbounded size: for every `N` the member `padding H N` is
one, with at least `N` rows and at least `N` columns. -/
theorem exists_counterexample_size_ge_general {k l : ℕ} (H : BMat k l) (hH : NoZeroLine H)
    (hcounter : ¬ PolyRemoval H) (N : ℕ) :
    ∃ (a b : ℕ) (P : BMat a b), N ≤ a ∧ N ≤ b ∧ NoZeroLine P ∧ ¬ PolyRemoval P :=
  exists_counterexample_size_ge H hH hcounter (fun X hX hc => padding_step X hX hc) N

end OrderedRemoval

#print axioms OrderedRemoval.infinite_family_of_counterexample
#print axioms OrderedRemoval.exists_injective_counterexample_family
#print axioms OrderedRemoval.exists_counterexample_size_ge_general

#print axioms OrderedRemoval.copyCount_blockDiag_one
#print axioms OrderedRemoval.copyCount_appendZeroCols

#print axioms OrderedRemoval.editDist_appendZeroCols

#print axioms OrderedRemoval.not_polyRemoval_appendZeroCols
