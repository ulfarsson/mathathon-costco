/-
Refutation of `editDist_blockDiag_one` (and hence of the general stage theorems)
for the degenerate empty pattern `H : BMat 0 0`, which satisfies `NoZeroLine`.
Self-contained: §1 definitions copied verbatim from Statements.lean.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Lattice.Nat

namespace OrderedRemoval

open Classical

abbrev BMat (a b : ℕ) := Fin a → Fin b → Bool

def IsCopy {k l n m : ℕ} (H : BMat k l) (A : BMat n m) (r : Fin k → Fin n) (c : Fin l → Fin m) :
    Prop :=
  StrictMono r ∧ StrictMono c ∧ ∀ i j, A (r i) (c j) = H i j

def Contains {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ∃ r c, IsCopy H A r c

def Free {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : Prop :=
  ¬ Contains H A

noncomputable def hamming {n m : ℕ} (A B : BMat n m) : ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin m => A x.1 x.2 ≠ B x.1 x.2)).card

noncomputable def editDist {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=
  sInf {d | ∃ B : BMat n m, Free H B ∧ hamming A B = d}

def blockDiag {k l p q : ℕ} (H : BMat k l) (Z : BMat p q) : BMat (k + p) (l + q) :=
  fun i j =>
    Fin.addCases (motive := fun _ => Bool)
      (fun i' => Fin.addCases (motive := fun _ => Bool) (fun j' => H i' j') (fun _ => false) j)
      (fun i' => Fin.addCases (motive := fun _ => Bool) (fun _ => false) (fun j' => Z i' j') j) i

def blowup {p q : ℕ} (Z : BMat p q) (n : ℕ) : BMat (p * q * n) (p * q * n) :=
  fun i j =>
    Z ⟨i.val / (q * n), Nat.div_lt_of_lt_mul (by
        have h := i.isLt
        simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩
      ⟨j.val / (p * n), Nat.div_lt_of_lt_mul (by
        have h := j.isLt
        simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h)⟩

def ones (a b : ℕ) : BMat a b := fun _ _ => true

def zeros (a b : ℕ) : BMat a b := fun _ _ => false

def NoZeroLine {k l : ℕ} (H : BMat k l) : Prop :=
  (∀ i, ∃ j, H i j = true) ∧ (∀ j, ∃ i, H i j = true)


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

/-- The Hamming distance from a matrix to itself is zero. -/
theorem hamming_self {n m : ℕ} (A : BMat n m) : hamming A A = 0 := by
  simp [hamming]

/-- `editDist H A = 0` iff `A` is `H`-free, provided an `H`-free matrix exists. -/
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

/-- The empty pattern is `NoZeroLine`. -/
theorem noZeroLine_empty : NoZeroLine (fun (_ : Fin 0) (_ : Fin 0) => false) :=
  ⟨fun i => i.elim0, fun j => j.elim0⟩

/-- Every matrix contains the empty pattern. -/
theorem contains_empty_pattern {n m : ℕ} (B : BMat n m) :
    Contains (fun (_ : Fin 0) (_ : Fin 0) => false) B :=
  ⟨fun i => i.elim0, fun i => i.elim0,
    fun a b hab => absurd a.isLt (Nat.not_lt_zero a.val),
    fun a b hab => absurd a.isLt (Nat.not_lt_zero a.val),
    fun i => i.elim0⟩

/-- Hence `editDist H A = 0` for the empty pattern. -/
theorem editDist_empty_pattern {n m : ℕ} (A : BMat n m) :
    editDist (fun (_ : Fin 0) (_ : Fin 0) => false) A = 0 := by
  rw [editDist]
  have hS : {d : ℕ | ∃ B : BMat n m,
      Free (fun (_ : Fin 0) (_ : Fin 0) => false) B ∧ hamming A B = d} = ∅ := by
    ext d
    constructor
    · rintro ⟨B, hB, -⟩
      exact hB (contains_empty_pattern B)
    · intro hd
      exact absurd hd (by simp)
  rw [hS, Nat.sInf_empty]

/-- The `(1,1)` entry of the concrete block matrix is `true`. -/
example : blockDiag (zeros 1 1) (ones 1 1) ⟨1, by decide⟩ ⟨1, by decide⟩ = true := rfl

/-- That concrete block matrix contains `ones 1 1`. -/
theorem contains_ones_of_blockDiag :
    Contains (ones 1 1) (blockDiag (zeros 1 1) (ones 1 1)) :=
  ⟨fun _ => ⟨1, by decide⟩, fun _ => ⟨1, by decide⟩,
    fun a b hab => absurd hab (by omega),
    fun a b hab => absurd hab (by omega),
    fun _ _ => rfl⟩

/-- `editDist (ones 1 1) X ≠ 0` for that matrix: a free matrix exists (`zeros`),
so distance zero would force `X` itself to be `ones 1 1`-free, which it is not. -/
theorem editDist_ones_blockDiag_ne_zero :
    editDist (ones 1 1) (blockDiag (zeros 1 1) (ones 1 1)) ≠ 0 := by
  intro h0
  have hex : ∃ B : BMat (1 + 1) (1 + 1), Free (ones 1 1) B :=
    ⟨zeros (1 + 1) (1 + 1), by
      rintro ⟨r, c, -, -, hrc⟩
      have := hrc 0 0
      exact Bool.noConfusion this⟩
  have hfree : Free (ones 1 1) (blockDiag (zeros 1 1) (ones 1 1)) := by
    have hspec := (editDist_eq_zero_iff_of_exists_free (ones 1 1)
      (blockDiag (zeros 1 1) (ones 1 1)) hex).mp h0
    exact hspec
  exact hfree contains_ones_of_blockDiag

/-- `blockDiag` of the empty pattern is the second block. -/
theorem blockDiag_empty_ones :
    blockDiag (fun (_ : Fin 0) (_ : Fin 0) => false) (ones 1 1) = ones 1 1 := by
  funext i j
  have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
  have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
  rw [hi, hj]
  rfl

/-- `blowup` of the all-ones pattern is the all-ones matrix. -/
theorem blowup_ones {p q n : ℕ} : blowup (ones p q) n = ones (p * q * n) (p * q * n) := rfl

/-- The frozen statement `editDist_blockDiag_one` is false at the empty pattern:
its conclusion fails for `H : BMat 0 0`, `A := zeros 1 1`. -/
theorem editDist_blockDiag_one_counterexample :
    ¬ (editDist (blockDiag (fun (_ : Fin 0) (_ : Fin 0) => false) (ones 1 1))
          (blockDiag (zeros 1 1) (ones 1 1)) =
        editDist (fun (_ : Fin 0) (_ : Fin 0) => false) (zeros 1 1)) := by
  intro h
  have hzero : editDist (fun (_ : Fin 0) (_ : Fin 0) => false) (zeros 1 1) = 0 :=
    editDist_empty_pattern (zeros 1 1)
  rw [hzero] at h
  rw [blockDiag_empty_ones] at h
  exact editDist_ones_blockDiag_ne_zero h

/-- The frozen statement `editDist_blockDiag` (§5) is likewise false at the empty
pattern: take `Z := ones 1 1`, `p = q = 1`, `A := zeros 1 1`, `n := 1`. -/
theorem editDist_blockDiag_counterexample :
    ¬ (editDist (blockDiag (fun (_ : Fin 0) (_ : Fin 0) => false) (ones 1 1))
          (blockDiag (zeros 1 1) (blowup (ones 1 1) 1)) =
        editDist (fun (_ : Fin 0) (_ : Fin 0) => false) (zeros 1 1)) := by
  intro h
  rw [editDist_empty_pattern] at h
  rw [blockDiag_empty_ones, blowup_ones] at h
  exact editDist_ones_blockDiag_ne_zero h

/-- There is no proof of the frozen §3 statement as universally stated. -/
theorem no_editDist_blockDiag_one :
    ¬ (∀ {k l n : ℕ} (H : BMat k l), NoZeroLine H → ∀ A : BMat n n,
        editDist (blockDiag H (ones 1 1)) (blockDiag A (ones n n)) = editDist H A) := by
  intro h
  exact editDist_blockDiag_one_counterexample
    (h (fun (_ : Fin 0) (_ : Fin 0) => false) noZeroLine_empty (zeros 1 1))

/-- There is no proof of the frozen §5 statement as universally stated. -/
theorem no_editDist_blockDiag :
    ¬ (∀ {k l p q n : ℕ} (H : BMat k l), NoZeroLine H → ∀ (Z : BMat p q), 0 < p → 0 < q →
        (Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) → ∀ A : BMat n n,
        editDist (blockDiag H Z) (blockDiag A (blowup Z n)) = editDist H A) := by
  intro h
  exact editDist_blockDiag_counterexample
    (h (fun (_ : Fin 0) (_ : Fin 0) => false) noZeroLine_empty (ones 1 1) (by decide) (by decide)
      (Or.inl (fun a b _ => Subsingleton.elim a b)) (zeros 1 1))

end OrderedRemoval

#print axioms OrderedRemoval.no_editDist_blockDiag_one
#print axioms OrderedRemoval.no_editDist_blockDiag
