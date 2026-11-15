/-
`red(H)`: delete every row equal to the row above it and every column equal to the column to its
left.  The duplication theorem in the paper's form: `H` satisfies the conjecture iff `red(H)` does.
-/
import OrderedRemoval.Dup.Main

namespace OrderedRemoval

open Classical

/-- The index map that skips position `i`: `0, …, i-1, i+1, …, k`. -/
def skipIdx {k : ℕ} (i : Fin (k + 1)) (a : Fin k) : Fin (k + 1) :=
  ⟨if a.val < i.val then a.val else a.val + 1, by have := a.isLt; split <;> omega⟩

@[simp] theorem skipIdx_val {k : ℕ} (i : Fin (k + 1)) (a : Fin k) :
    (skipIdx i a).val = if a.val < i.val then a.val else a.val + 1 := rfl

/-- `H` with row `i` deleted. -/
def deleteRow {k l : ℕ} (H : BMat (k + 1) l) (i : Fin (k + 1)) : BMat k l :=
  fun a b => H (skipIdx i a) b

/-- Deleting row `a+1` when it equals row `a`, then writing row `a` twice, gives `H` back. -/
theorem dupRow_deleteRow {k l : ℕ} (H : BMat (k + 1) l) (a : Fin k)
    (h : ∀ b, H a.castSucc b = H a.succ b) : dupRow (deleteRow H a.succ) a = H := by
  funext x b
  simp only [dupRow, deleteRow]
  by_cases hx : x.val = a.val + 1
  · have e1 : skipIdx a.succ (dupIdx a x) = a.castSucc := by
      ext; simp only [skipIdx_val, dupIdx_val, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> omega
    have e2 : x = a.succ := by ext; simp; omega
    rw [e1, e2, h]
  · congr 1
    ext; simp only [skipIdx_val, dupIdx_val, Fin.val_succ]
    have := x.isLt; split_ifs <;> omega

/-- Delete, from the top, each row equal to the row above it. -/
noncomputable def redRows : (k l : ℕ) → BMat k l → Σ k', BMat k' l
  | 0, _, H => ⟨0, H⟩
  | k + 1, l, H =>
    if h : ∃ a : Fin k, ∀ b, H a.castSucc b = H a.succ b then
      redRows k l (deleteRow H (Classical.choose h).succ)
    else ⟨k + 1, H⟩

/-- Neighbouring rows differ. -/
def RowsReduced {k l : ℕ} (R : BMat k l) : Prop :=
  ∀ a a' : Fin k, a'.val = a.val + 1 → ∃ b, R a b ≠ R a' b

theorem infl_trans {k₀ l₀ k₁ l₁ k l : ℕ} {R : BMat k₀ l₀} {M : BMat k₁ l₁} {H : BMat k l}
    (h₁ : Infl R M) (h₂ : Infl M H) : Infl R H := by
  induction h₂ with
  | refl => exact h₁
  | col j _ ih => exact Infl.col j (ih h₁)
  | row i _ ih => exact Infl.row i (ih h₁)

theorem infl_tr {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H) :
    Infl (tr R) (tr H) := by
  induction hI with
  | refl => exact Infl.refl _
  | col j _ ih => exact Infl.row j ih
  | row i _ ih => exact Infl.col i ih

theorem redRows_spec : ∀ (k l : ℕ) (H : BMat k l),
    Infl (redRows k l H).2 H ∧ RowsReduced (redRows k l H).2 ∧ (0 < k → 0 < (redRows k l H).1)
  | 0, l, H => by
    refine ⟨by simp only [redRows]; exact Infl.refl _, ?_, fun h => absurd h (lt_irrefl 0)⟩
    simp only [redRows]; intro a; exact a.elim0
  | k + 1, l, H => by
    by_cases h : ∃ a : Fin k, ∀ b, H a.castSucc b = H a.succ b
    · have hred : redRows (k + 1) l H = redRows k l (deleteRow H (Classical.choose h).succ) := by
        simp only [redRows, dif_pos h]
      obtain ⟨ih1, ih2, ih3⟩ := redRows_spec k l (deleteRow H (Classical.choose h).succ)
      rw [hred]
      refine ⟨?_, ih2, fun _ => ih3 ?_⟩
      · have := Infl.row (Classical.choose h) ih1
        rwa [dupRow_deleteRow H _ (Classical.choose_spec h)] at this
      · exact Nat.pos_of_ne_zero (fun h0 => by subst h0; exact (Classical.choose h).elim0)
    · have hred : redRows (k + 1) l H = ⟨k + 1, H⟩ := by simp only [redRows, dif_neg h]
      rw [hred]
      refine ⟨Infl.refl _, ?_, fun _ => Nat.succ_pos k⟩
      intro a a' ha
      have ha' : a'.val < k + 1 := a'.isLt
      by_contra hne
      push Not at hne
      apply h
      refine ⟨⟨a.val, by omega⟩, fun b => ?_⟩
      have e1 : (⟨a.val, by omega⟩ : Fin k).castSucc = a := by ext; simp
      have e2 : (⟨a.val, by omega⟩ : Fin k).succ = a' := by ext; simp; omega
      rw [e1, e2]; exact hne b

/-- Deleting repeated rows keeps neighbouring columns distinct. -/
theorem redRows_colsReduced : ∀ (k l : ℕ) (H : BMat k l), RowsReduced (tr H) →
    RowsReduced (tr (redRows k l H).2)
  | 0, l, H, hH => by simpa only [redRows] using hH
  | k + 1, l, H, hH => by
    by_cases h : ∃ a : Fin k, ∀ b, H a.castSucc b = H a.succ b
    · have hred : redRows (k + 1) l H = redRows k l (deleteRow H (Classical.choose h).succ) := by
        simp only [redRows, dif_pos h]
      rw [hred]
      apply redRows_colsReduced
      intro b b' hb
      obtain ⟨x, hx⟩ := hH b b' hb
      set a := Classical.choose h
      have ha := Classical.choose_spec h
      simp only [tr, deleteRow] at hx ⊢
      by_cases hxa : x.val = a.val + 1
      · have ex : x = a.succ := by ext; simp; omega
        refine ⟨a, ?_⟩
        have e1 : skipIdx a.succ a = a.castSucc := by ext; simp
        rw [e1, ha b, ha b', ← ex]; exact hx
      · refine ⟨⟨if x.val < a.val + 1 then x.val else x.val - 1, by
          have := x.isLt; split <;> omega⟩, ?_⟩
        have e1 : skipIdx a.succ ⟨if x.val < a.val + 1 then x.val else x.val - 1, by
            have := x.isLt; split <;> omega⟩ = x := by
          ext; simp only [skipIdx_val, Fin.val_succ]; split_ifs <;> omega
        rw [e1]; exact hx
    · have hred : redRows (k + 1) l H = ⟨k + 1, H⟩ := by simp only [redRows, dif_neg h]
      rw [hred]; exact hH

/-- `red(H)`: first delete repeated rows, then repeated columns. -/
noncomputable def red {k l : ℕ} (H : BMat k l) : Pattern :=
  let P := redRows k l H
  let Q := redRows l P.1 (tr P.2)
  ⟨(P.1, Q.1), tr Q.2⟩

theorem infl_red {k l : ℕ} (H : BMat k l) : Infl (red H).2 H := by
  obtain ⟨h1, -, -⟩ := redRows_spec k l H
  obtain ⟨h2, -, -⟩ := redRows_spec l _ (tr (redRows k l H).2)
  exact infl_trans (infl_tr h2) h1

theorem reduced_red {k l : ℕ} (H : BMat k l) : Reduced (red H).2 := by
  obtain ⟨-, hP, -⟩ := redRows_spec k l H
  obtain ⟨-, hQ, -⟩ := redRows_spec l _ (tr (redRows k l H).2)
  have hQc := redRows_colsReduced l _ (tr (redRows k l H).2) hP
  refine ⟨fun a a' ha => hQc a a' ha, fun b b' hb => hQ b b' hb⟩

theorem red_pos {k l : ℕ} (H : BMat k l) (hk : 0 < k) (hl : 0 < l) :
    0 < (red H).1.1 ∧ 0 < (red H).1.2 :=
  ⟨(redRows_spec k l H).2.2 hk, (redRows_spec l _ (tr (redRows k l H).2)).2.2 hl⟩

/-- **Duplication theorem** (Theorem 11 of the paper): `H` satisfies the conjecture if and only if
`red(H)` does. -/
theorem polyRemoval_iff_red {k l : ℕ} (H : BMat k l) (hk : 0 < k) (hl : 0 < l) :
    PolyRemoval H ↔ PolyRemoval (red H).2 :=
  polyRemoval_iff_of_infl (infl_red H) (reduced_red H) (red_pos H hk hl).1 (red_pos H hk hl).2

end OrderedRemoval
