/-
Duplication theorem: definitions.

Paper notation → Lean:
  H with column j written twice          `dupCol H j`   (k × (l+1))
  H with row i written twice             `dupRow H i`   ((k+1) × l)
  Hᵀ                                     `tr H`
  "H is obtained from R by repeating rows and columns"   `Infl R H`
  "no two equal neighbouring rows or columns"            `Reduced R`
  A^(q) (each entry a constant q × q block)              `hostBlowup A q`  (size n·q)

Indices are 0-based.
-/
import OrderedRemoval.Statements

namespace OrderedRemoval

open Classical

/-- The index map that writes position `j` twice: `0, …, j, j, j+1, …, l-1`. -/
def dupIdx {l : ℕ} (j : Fin l) (b : Fin (l + 1)) : Fin l :=
  ⟨if b.val ≤ j.val then b.val else b.val - 1, by
    have := b.isLt; have := j.isLt; split <;> omega⟩

@[simp] theorem dupIdx_val {l : ℕ} (j : Fin l) (b : Fin (l + 1)) :
    (dupIdx j b).val = if b.val ≤ j.val then b.val else b.val - 1 := rfl

/-- `H` with column `j` written twice in a row. -/
def dupCol {k l : ℕ} (H : BMat k l) (j : Fin l) : BMat k (l + 1) :=
  fun a b => H a (dupIdx j b)

/-- `H` with row `i` written twice in a row. -/
def dupRow {k l : ℕ} (H : BMat k l) (i : Fin k) : BMat (k + 1) l :=
  fun a b => H (dupIdx i a) b

/-- The transpose. -/
def tr {k l : ℕ} (H : BMat k l) : BMat l k := fun j i => H i j

/-- `Infl R H`: `H` is obtained from `R` by repeatedly writing a row or a column twice. -/
inductive Infl : {k₀ l₀ k l : ℕ} → BMat k₀ l₀ → BMat k l → Prop
  | refl {k l : ℕ} (R : BMat k l) : Infl R R
  | col {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (j : Fin l) :
      Infl R H → Infl R (dupCol H j)
  | row {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (i : Fin k) :
      Infl R H → Infl R (dupRow H i)

/-- No two equal neighbouring rows and no two equal neighbouring columns. -/
def Reduced {k l : ℕ} (R : BMat k l) : Prop :=
  (∀ a a' : Fin k, a'.val = a.val + 1 → ∃ b, R a b ≠ R a' b) ∧
  (∀ b b' : Fin l, b'.val = b.val + 1 → ∃ a, R a b ≠ R a b')

theorem div_lt_of_lt_mul' {n q : ℕ} (i : Fin (n * q)) : i.val / q < n :=
  Nat.div_lt_of_lt_mul (by have h := i.isLt; simpa [Nat.mul_comm] using h)

/-- `A^(q)`: every entry of `A` replaced by a constant `q × q` block.
Row `i` lies in block `i / q`. -/
def hostBlowup {n : ℕ} (A : BMat n n) (q : ℕ) : BMat (n * q) (n * q) :=
  fun i j => A ⟨i.val / q, div_lt_of_lt_mul' i⟩ ⟨j.val / q, div_lt_of_lt_mul' j⟩

end OrderedRemoval
