/-
Fact 1: many copies of `H` give many copies of `H` with one row or column repeated,
and its iteration along `Infl`.
-/
import OrderedRemoval.Dup.Defs
import Mathlib.Algebra.Order.Chebyshev

namespace OrderedRemoval

open Classical

theorem tr_tr {k l : ℕ} (H : BMat k l) : tr (tr H) = H := rfl

theorem tr_dupRow {k l : ℕ} (H : BMat k l) (i : Fin k) : tr (dupRow H i) = dupCol (tr H) i := rfl

namespace Fact1Aux

/-- The `i`-th position other than `j`. -/
def skip {l' : ℕ} (j : Fin (l' + 1)) (i : Fin l') : Fin (l' + 1) :=
  ⟨if i.val < j.val then i.val else i.val + 1, by have := i.isLt; split <;> omega⟩

/-- The frame of a copy: its columns with column `j` removed. -/
def key {k l' n : ℕ} (j : Fin (l' + 1)) (rc : (Fin k → Fin n) × (Fin (l' + 1) → Fin n)) :
    (Fin k → Fin n) × (Fin l' → Fin n) :=
  (rc.1, fun i => rc.2 (skip j i))

theorem key_eq {k l' n : ℕ} {j : Fin (l' + 1)} {u v : (Fin k → Fin n) × (Fin (l' + 1) → Fin n)}
    (h : key j u = key j v) : u.1 = v.1 ∧ ∀ b, b ≠ j → u.2 b = v.2 b := by
  simp only [key, Prod.mk.injEq] at h
  refine ⟨h.1, fun b hb => ?_⟩
  have hb' : b.val ≠ j.val := fun h' => hb (Fin.ext h')
  have := b.isLt
  have := j.isLt
  obtain ⟨i, hi⟩ : ∃ i : Fin l', skip j i = b := by
    by_cases hbj : b.val < j.val
    · exact ⟨⟨b.val, by omega⟩, Fin.ext (by simp [skip, hbj])⟩
    · refine ⟨⟨b.val - 1, by omega⟩, Fin.ext ?_⟩
      show (if b.val - 1 < j.val then b.val - 1 else b.val - 1 + 1) = b.val
      split <;> omega
  rw [← hi]
  exact congrFun h.2 i

/-- Merge two copies with the same frame into a copy of `dupCol H j`. -/
def merge {k l' n : ℕ} (j : Fin (l' + 1))
    (p : ((Fin k → Fin n) × (Fin (l' + 1) → Fin n)) × ((Fin k → Fin n) × (Fin (l' + 1) → Fin n))) :
    (Fin k → Fin n) × (Fin (l' + 1 + 1) → Fin n) :=
  (p.1.1, fun b => if b.val ≤ j.val then p.1.2 (dupIdx j b) else p.2.2 (dupIdx j b))

theorem merge_copy {k l' n : ℕ} (H : BMat k (l' + 1)) (j : Fin (l' + 1)) (B : BMat n n)
    {u v : (Fin k → Fin n) × (Fin (l' + 1) → Fin n)}
    (hu : IsCopy H B u.1 u.2) (hv : IsCopy H B v.1 v.2) (hk : key j u = key j v)
    (hlt : u.2 j < v.2 j) :
    IsCopy (dupCol H j) B (merge j (u, v)).1 (merge j (u, v)).2 := by
  obtain ⟨h1, hag⟩ := key_eq hk
  refine ⟨hu.1, ?_, ?_⟩
  · intro b1 b2 h12
    rw [Fin.lt_def] at h12
    simp only [merge]
    split_ifs with hb1 hb2 hb2
    · apply hu.2.1
      rw [Fin.lt_def, dupIdx_val, dupIdx_val, if_pos hb1, if_pos hb2]
      exact h12
    · by_cases hx : dupIdx j b2 = j
      · rw [hx]
        refine lt_of_le_of_lt (hu.2.1.monotone ?_) hlt
        rw [Fin.le_iff_val_le_val, dupIdx_val, if_pos hb1]
        exact hb1
      · have hxv : (dupIdx j b2).val ≠ j.val := fun h => hx (Fin.ext h)
        rw [dupIdx_val, if_neg hb2] at hxv
        rw [← hag _ hx]
        apply hu.2.1
        rw [Fin.lt_def, dupIdx_val, dupIdx_val, if_pos hb1, if_neg hb2]
        omega
    · omega
    · apply hv.2.1
      rw [Fin.lt_def, dupIdx_val, dupIdx_val, if_neg hb1, if_neg hb2]
      omega
  · intro a b
    simp only [merge, dupCol]
    split_ifs with hb
    · exact hu.2.2 a _
    · rw [h1]
      exact hv.2.2 a _

def lift1 {l' : ℕ} (j : Fin (l' + 1)) (x : Fin (l' + 1)) : Fin (l' + 1 + 1) :=
  ⟨if x.val ≤ j.val then x.val else x.val + 1, by have := x.isLt; split <;> omega⟩

def lift2 {l' : ℕ} (j : Fin (l' + 1)) (x : Fin (l' + 1)) : Fin (l' + 1 + 1) :=
  ⟨if x.val < j.val then x.val else x.val + 1, by have := x.isLt; split <;> omega⟩

theorem recover1 {k l' n : ℕ} {j : Fin (l' + 1)} {u v : (Fin k → Fin n) × (Fin (l' + 1) → Fin n)}
    (hk : key j u = key j v) (x : Fin (l' + 1)) :
    u.2 x = (merge j (u, v)).2 (lift1 j x) := by
  obtain ⟨-, hag⟩ := key_eq hk
  simp only [merge]
  by_cases hx : x.val ≤ j.val
  · have e : (lift1 j x).val = x.val := by simp [lift1, hx]
    rw [if_pos (show (lift1 j x).val ≤ j.val by omega)]
    refine congrArg u.2 (Fin.ext ?_)
    rw [dupIdx_val, e, if_pos hx]
  · have e : (lift1 j x).val = x.val + 1 := by simp [lift1, hx]
    rw [if_neg (show ¬ (lift1 j x).val ≤ j.val by omega)]
    have ex : dupIdx j (lift1 j x) = x := by
      ext
      rw [dupIdx_val, e, if_neg (by omega)]
      omega
    rw [ex]
    exact hag x (fun h => hx (by rw [h]))

theorem recover2 {k l' n : ℕ} {j : Fin (l' + 1)} {u v : (Fin k → Fin n) × (Fin (l' + 1) → Fin n)}
    (hk : key j u = key j v) (x : Fin (l' + 1)) :
    v.2 x = (merge j (u, v)).2 (lift2 j x) := by
  obtain ⟨-, hag⟩ := key_eq hk
  simp only [merge]
  by_cases hx : x.val < j.val
  · have e : (lift2 j x).val = x.val := by simp [lift2, hx]
    rw [if_pos (show (lift2 j x).val ≤ j.val by omega)]
    have ex : dupIdx j (lift2 j x) = x := by
      ext
      rw [dupIdx_val, e, if_pos (by omega)]
    rw [ex]
    exact (hag x (fun h => by rw [h] at hx; exact lt_irrefl _ hx)).symm
  · have e : (lift2 j x).val = x.val + 1 := by simp [lift2, hx]
    rw [if_neg (show ¬ (lift2 j x).val ≤ j.val by omega)]
    refine congrArg v.2 (Fin.ext ?_)
    rw [dupIdx_val, e, if_neg (by omega)]
    omega

theorem main {k l' n : ℕ} (H : BMat k (l' + 1)) (j : Fin (l' + 1)) (B : BMat n n) :
    copyCount H B ^ 2 * n ≤
      (2 * copyCount (dupCol H j) B + copyCount H B) * n ^ (k + (l' + 1)) := by
  set S := Finset.univ.filter
    (fun rc : (Fin k → Fin n) × (Fin (l' + 1) → Fin n) => IsCopy H B rc.1 rc.2) with hS
  set S' := Finset.univ.filter
    (fun rc : (Fin k → Fin n) × (Fin (l' + 1 + 1) → Fin n) => IsCopy (dupCol H j) B rc.1 rc.2)
    with hS'
  have hN : copyCount H B = S.card := rfl
  have hN' : copyCount (dupCol H j) B = S'.card := rfl
  rw [hN, hN']
  set x : (Fin k → Fin n) × (Fin l' → Fin n) → ℕ :=
    fun F => (S.filter (fun u => key j u = F)).card with hx
  have h1 : S.card = ∑ F, x F :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  set P2 := (S ×ˢ S).filter (fun p => key j p.1 = key j p.2) with hP2
  have h2 : P2.card = ∑ F, x F ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => key j p.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl (fun F _ => ?_)
    rw [sq, hx, ← Finset.card_product]
    congr 1
    ext ⟨u, v⟩
    simp only [P2, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hF⟩
      exact ⟨⟨hu, hF⟩, hv, huv ▸ hF⟩
    · rintro ⟨⟨hu, hF⟩, hv, hF'⟩
      exact ⟨⟨⟨hu, hv⟩, hF.trans hF'.symm⟩, hF⟩
  have hCS : (∑ F, x F) ^ 2 ≤ Fintype.card ((Fin k → Fin n) × (Fin l' → Fin n)) * ∑ F, x F ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  set Lt := P2.filter (fun p => p.1.2 j < p.2.2 j) with hLt
  set Gt := P2.filter (fun p => p.2.2 j < p.1.2 j) with hGt
  set D := P2.filter (fun p => p.1 = p.2) with hD
  have hsub : P2 ⊆ D ∪ Lt ∪ Gt := by
    intro p hp
    simp only [Finset.mem_union, D, Lt, Gt, Finset.mem_filter]
    rcases lt_trichotomy (p.1.2 j) (p.2.2 j) with h | h | h
    · exact Or.inl (Or.inr ⟨hp, h⟩)
    · refine Or.inl (Or.inl ⟨hp, ?_⟩)
      have hk := (Finset.mem_filter.1 hp).2
      obtain ⟨h1, hag⟩ := key_eq hk
      refine Prod.ext h1 (funext fun b => ?_)
      by_cases hb : b = j
      · rw [hb]; exact h
      · exact hag b hb
    · exact Or.inr ⟨hp, h⟩
  have hDc : D.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      have hp := Finset.mem_coe.1 hp
      simp only [D, P2, Finset.mem_filter, Finset.mem_product] at hp
      exact Finset.mem_coe.2 hp.1.1.1
    · intro p hp q hq hpq
      have hp := Finset.mem_coe.1 hp
      have hq := Finset.mem_coe.1 hq
      simp only [D, Finset.mem_filter] at hp hq
      exact Prod.ext hpq (hp.2.symm.trans (hpq.trans hq.2))
  have hGc : Gt.card = Lt.card := by
    refine Finset.card_equiv (Equiv.prodComm _ _) (fun p => ?_)
    simp only [Gt, Lt, P2, Finset.mem_filter, Finset.mem_product, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap]
    constructor
    · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩; exact ⟨⟨⟨b, a⟩, c.symm⟩, d⟩
    · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩; exact ⟨⟨⟨b, a⟩, c.symm⟩, d⟩
  have hLc : Lt.card ≤ S'.card := by
    refine Finset.card_le_card_of_injOn (merge j) ?_ ?_
    · intro p hp
      have hp := Finset.mem_coe.1 hp
      simp only [Lt, P2, S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_univ _, merge_copy H j B hp.1.1.1 hp.1.1.2 hp.1.2 hp.2⟩)
    · rintro ⟨u, v⟩ hp ⟨u', v'⟩ hq hpq
      have hp := Finset.mem_coe.1 hp
      have hq := Finset.mem_coe.1 hq
      simp only [Lt, P2, Finset.mem_filter] at hp hq
      have hk := hp.1.2
      have hk' := hq.1.2
      obtain ⟨hu1, -⟩ := key_eq hk
      obtain ⟨hu1', -⟩ := key_eq hk'
      have e1 : u.1 = u'.1 := by have := congrArg Prod.fst hpq; exact this
      have e2 : u.2 = u'.2 := funext fun y => by
        rw [recover1 hk, recover1 hk', hpq]
      have e3 : v.2 = v'.2 := funext fun y => by
        rw [recover2 hk, recover2 hk', hpq]
      have e4 : v.1 = v'.1 := hu1.symm.trans (e1.trans hu1')
      exact Prod.ext (Prod.ext e1 e2) (Prod.ext e4 e3)
  have hP : P2.card ≤ S.card + 2 * S'.card := by
    calc P2.card ≤ (D ∪ Lt ∪ Gt).card := Finset.card_le_card hsub
      _ ≤ D.card + Lt.card + Gt.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ S.card + 2 * S'.card := by omega
  have hT : Fintype.card ((Fin k → Fin n) × (Fin l' → Fin n)) * n = n ^ (k + (l' + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  calc S.card ^ 2 * n
      ≤ Fintype.card ((Fin k → Fin n) × (Fin l' → Fin n)) * P2.card * n := by
        apply Nat.mul_le_mul_right
        rw [h1, h2]; exact hCS
    _ ≤ Fintype.card ((Fin k → Fin n) × (Fin l' → Fin n)) * (S.card + 2 * S'.card) * n := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_left _ hP
    _ = (2 * S'.card + S.card) * n ^ (k + (l' + 1)) := by
        rw [← hT]; ring

end Fact1Aux

/-- `N_H(B) = N_{Hᵀ}(Bᵀ)`. -/
theorem copyCount_tr {k l n m : ℕ} (H : BMat k l) (B : BMat n m) :
    copyCount (tr H) (tr B) = copyCount H B := by
  rw [copyCount, copyCount]
  refine Finset.card_equiv (Equiv.prodComm _ _) (fun p => ?_)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  unfold IsCopy tr
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun i j => h3 j i⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun i j => h3 j i⟩

/-- Fact 1 (column), counting form: with `N = N_H(B)` and `N' = N_{H'}(B)` for `H'` = `H` with
column `j` repeated, `N² ≤ T (N + 2N')` where `T ≤ n^(k+l-1)` is the number of frames;
multiplied by `n` to avoid `l - 1`. -/
theorem fact1_col {k l n : ℕ} (H : BMat k l) (j : Fin l) (B : BMat n n) :
    copyCount H B ^ 2 * n ≤ (2 * copyCount (dupCol H j) B + copyCount H B) * n ^ (k + l) := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := j.isLt; omega⟩
  exact Fact1Aux.main H j B

/-- Fact 1 (row), by transposing. -/
theorem fact1_row {k l n : ℕ} (H : BMat k l) (i : Fin k) (B : BMat n n) :
    copyCount H B ^ 2 * n ≤ (2 * copyCount (dupRow H i) B + copyCount H B) * n ^ (k + l) := by
  have h := fact1_col (tr H) i (tr B)
  rw [← tr_dupRow, copyCount_tr, copyCount_tr, Nat.add_comm l k] at h
  exact h

/-- Fact 1, density form ("in particular" in the paper): if `N ≥ δ n^e` and `n ≥ 2/δ`,
then `N' ≥ (δ²/4) n^(e+1)`. -/
theorem density_step {N N' n e : ℕ} (h : N ^ 2 * n ≤ (2 * N' + N) * n ^ e) (δ : ℝ) (hδ : 0 < δ)
    (hN : δ * (n : ℝ) ^ e ≤ N) (hn : 2 / δ ≤ n) :
    δ ^ 2 / 4 * (n : ℝ) ^ (e + 1) ≤ N' := by
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (div_pos two_pos hδ) hn
  have hM : (0:ℝ) < (n:ℝ) ^ e := pow_pos hn0 e
  have hr : ((N:ℝ)) ^ 2 * n ≤ (2 * N' + N) * (n:ℝ) ^ e := by exact_mod_cast h
  have hδn : 2 ≤ δ * n := by rw [div_le_iff₀ hδ] at hn; linarith
  rw [pow_succ (n : ℝ) e]
  set M := (n:ℝ) ^ e
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have h1 : 2 * M ≤ N * n := by
    nlinarith [mul_le_mul_of_nonneg_right hδn hM.le, mul_le_mul_of_nonneg_right hN hn0.le]
  have h2 : (N:ℝ) ^ 2 * n ≤ 4 * N' * M := by
    nlinarith [mul_nonneg hN0 (sub_nonneg.2 h1)]
  have h3 : (δ * M) ^ 2 ≤ (N:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
  refine le_of_mul_le_mul_right ?_ hM
  nlinarith [mul_le_mul_of_nonneg_right h3 hn0.le]

namespace Fact1Aux

theorem step {N N' n e K : ℕ} {d : ℝ} (hfact : N ^ 2 * n ≤ (2 * N' + N) * n ^ e)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hK : 2 * (4 / d) ^ K ≤ (n : ℝ) → (d / 4) ^ K * (n : ℝ) ^ e ≤ N)
    (hn : 2 * (4 / d) ^ (2 * K + 1) ≤ (n : ℝ)) :
    (d / 4) ^ (2 * K + 1) * (n : ℝ) ^ (e + 1) ≤ N' := by
  have hq : 1 ≤ 4 / d := by rw [le_div_iff₀ hd]; linarith
  have hpow : (4 / d) ^ K ≤ (4 / d) ^ (2 * K + 1) := pow_le_pow_right₀ hq (by omega)
  have hH := hK (by linarith)
  have hδ : 0 < (d / 4) ^ K := by positivity
  have hn' : 2 / (d / 4) ^ K ≤ n := by
    have : 2 / (d / 4) ^ K = 2 * (4 / d) ^ K := by
      rw [div_pow, div_pow]; field_simp
    rw [this]; linarith
  have hs := density_step hfact _ hδ hH hn'
  have hX : 0 ≤ (n : ℝ) ^ (e + 1) := by positivity
  have hc : (d / 4) ^ (2 * K + 1) ≤ ((d / 4) ^ K) ^ 2 / 4 := by
    rw [← pow_mul, pow_succ, mul_comm K 2]
    have : 0 ≤ (d / 4) ^ (2 * K) := by positivity
    nlinarith
  calc (d / 4) ^ (2 * K + 1) * (n : ℝ) ^ (e + 1)
      ≤ ((d / 4) ^ K) ^ 2 / 4 * (n : ℝ) ^ (e + 1) := mul_le_mul_of_nonneg_right hc hX
    _ ≤ N' := hs

end Fact1Aux

/-- Fact 1 applied once for each repeated row or column. -/
theorem infl_density {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (n : ℕ) (B : BMat n n) (d : ℝ), 0 < d → d ≤ 1 →
      d * (n : ℝ) ^ (k₀ + l₀) ≤ copyCount R B → 2 * (4 / d) ^ K ≤ (n : ℝ) →
        (d / 4) ^ K * (n : ℝ) ^ (k + l) ≤ copyCount H B := by
  induction hI with
  | refl R =>
    refine ⟨1, le_rfl, fun n B d hd _ hR _ => le_trans ?_ hR⟩
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  | col j _ ih =>
    obtain ⟨K, hK, hKp⟩ := ih
    refine ⟨2 * K + 1, by omega, fun n B d hd hd1 hR hn => ?_⟩
    rw [← Nat.add_assoc]
    exact Fact1Aux.step (fact1_col _ j B) hd hd1 (hKp n B d hd hd1 hR) hn
  | row i _ ih =>
    obtain ⟨K, hK, hKp⟩ := ih
    refine ⟨2 * K + 1, by omega, fun n B d hd hd1 hR hn => ?_⟩
    rw [Nat.add_right_comm]
    exact Fact1Aux.step (fact1_row _ i B) hd hd1 (hKp n B d hd hd1 hR) hn

end OrderedRemoval
