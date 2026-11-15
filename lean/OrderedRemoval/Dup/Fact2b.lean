/-
Fact 2(b): far stays far.
-/
import OrderedRemoval.Dup.Fact1
import OrderedRemoval.Dup.Repr

namespace OrderedRemoval

open Classical

namespace Fact2bAux

/-- The position `i * q + u` in `Fin (n * q)`. -/
def pos {n q : ℕ} (i : Fin n) (u : Fin q) : Fin (n * q) :=
  ⟨i.val * q + u.val, by
    have hi := i.isLt; have hu := u.isLt
    calc i.val * q + u.val < i.val * q + q := by omega
      _ = (i.val + 1) * q := by ring
      _ ≤ n * q := Nat.mul_le_mul_right _ hi⟩

theorem pos_div {n q : ℕ} (i : Fin n) (u : Fin q) : (pos i u).val / q = i.val := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) u.isLt
  simp only [pos]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt u.isLt, Nat.zero_add]

theorem pos_mod {n q : ℕ} (i : Fin n) (u : Fin q) : (pos i u).val % q = u.val := by
  simp only [pos]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.isLt]

theorem pos_inj {n q : ℕ} {i i' : Fin n} {u u' : Fin q} (h : pos i u = pos i' u') :
    i = i' ∧ u = u' := by
  have h1 := pos_div i u
  have h2 := pos_mod i u
  rw [h, pos_div] at h1
  rw [h, pos_mod] at h2
  exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩

theorem pos_lt {n q : ℕ} {i i' : Fin n} (u u' : Fin q) (h : i < i') : pos i u < pos i' u' := by
  rw [Fin.lt_def] at h ⊢
  simp only [pos]
  have hu := u.isLt
  have h1 : (i.val + 1) * q ≤ i'.val * q := Nat.mul_le_mul_right _ h
  have h2 : (i.val + 1) * q = i.val * q + q := by ring
  have h3 : 0 ≤ u'.val := Nat.zero_le _
  linarith

theorem hostBlowup_pos {n q : ℕ} (A : BMat n n) (i j : Fin n) (u v : Fin q) :
    hostBlowup A q (pos i u) (pos j v) = A i j := by
  simp only [hostBlowup]
  congr 1 <;> exact Fin.ext (pos_div _ _)

/-- The `n × n` submatrix of `B` picked by `p`. -/
def pick {n q : ℕ} (B : BMat (n * q) (n * q)) (p : (Fin n → Fin q) × (Fin n → Fin q)) :
    BMat n n :=
  fun i j => B (pos i (p.1 i)) (pos j (p.2 j))

theorem card_mul_le {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ z ∈ s, f z ∈ t) (c M : ℕ)
    (h : ∀ b ∈ t, (s.filter (fun z => f z = b)).card * c ≤ M) :
    s.card * c ≤ M * t.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t) (by intro z hz; exact hf z hz),
    Finset.sum_mul]
  calc ∑ b ∈ t, (s.filter (fun z => f z = b)).card * c ≤ ∑ _b ∈ t, M := Finset.sum_le_sum h
    _ = M * t.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_mul_le' {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ z ∈ s, f z ∈ t) (c M : ℕ)
    (h : ∀ z0 ∈ s, ∃ C : Finset α, (∀ z ∈ s, f z = f z0 → z ∈ C) ∧ C.card * c ≤ M) :
    s.card * c ≤ M * t.card := by
  apply card_mul_le s t f hf c M
  intro b _
  rcases (s.filter (fun z => f z = b)).eq_empty_or_nonempty with he | ⟨z0, hz0⟩
  · rw [he]; simp
  · rw [Finset.mem_filter] at hz0
    obtain ⟨C, hC, hCc⟩ := h z0 hz0.1
    refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_)) hCc
    intro z hz
    rw [Finset.mem_filter] at hz
    exact hC z hz.1 (hz.2.trans hz0.2.symm)

theorem constr_card {n q a b : ℕ} (ρ : Fin a → Fin n) (hρ : Function.Injective ρ)
    (γ : Fin b → Fin n) (hγ : Function.Injective γ) (p0 : (Fin n → Fin q) × (Fin n → Fin q)) :
    (Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
      (∀ x, p.1 (ρ x) = p0.1 (ρ x)) ∧ ∀ y, p.2 (γ y) = p0.2 (γ y))).card * q ^ (a + b) =
      q ^ n * q ^ n := by
  have h1 := card_constrained (X := Fin q) ρ hρ (fun x => {p0.1 (ρ x)}) 1 (fun x => by simp)
  have h2 := card_constrained (X := Fin q) γ hγ (fun y => {p0.2 (γ y)}) 1 (fun y => by simp)
  simp only [Finset.mem_singleton, one_pow, one_mul, Fintype.card_fin] at h1 h2
  have hE : (Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
      (∀ x, p.1 (ρ x) = p0.1 (ρ x)) ∧ ∀ y, p.2 (γ y) = p0.2 (γ y))) =
      (Finset.univ.filter (fun f : Fin n → Fin q => ∀ x, f (ρ x) = p0.1 (ρ x))) ×ˢ
      (Finset.univ.filter (fun g : Fin n → Fin q => ∀ y, g (γ y) = p0.2 (γ y))) := by
    ext ⟨f, g⟩; simp
  rw [hE, Finset.card_product, pow_add]
  calc _ = ((Finset.univ.filter (fun f : Fin n → Fin q => ∀ x, f (ρ x) = p0.1 (ρ x))).card * q ^ a) *
      ((Finset.univ.filter (fun g : Fin n → Fin q => ∀ y, g (γ y) = p0.2 (γ y))).card * q ^ b) := by
        ring
    _ = _ := by rw [h1, h2]

theorem averaging {n q : ℕ} (A : BMat n n) (B : BMat (n * q) (n * q)) :
    (∑ p : (Fin n → Fin q) × (Fin n → Fin q), hamming A (pick B p)) * q ^ (1 + 1) ≤
      q ^ n * q ^ n * hamming (hostBlowup A q) B := by
  have hsum : (∑ p : (Fin n → Fin q) × (Fin n → Fin q), hamming A (pick B p)) =
      (Finset.univ.filter (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) × (Fin n × Fin n) =>
        A z.2.1 z.2.2 ≠ pick B z.1 z.2.1 z.2.2)).card := by
    simp only [hamming, Finset.card_filter, Fintype.sum_prod_type]
  rw [hsum]
  unfold hamming
  apply card_mul_le' _ _ (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) × (Fin n × Fin n) =>
    (pos z.2.1 (z.1.1 z.2.1), pos z.2.2 (z.1.2 z.2.2)))
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [hostBlowup_pos]; exact hz
  · intro z0 _
    have hinj : Function.Injective (fun _ : Fin 1 => z0.2.1) := fun x y _ => Subsingleton.elim x y
    have hinj' : Function.Injective (fun _ : Fin 1 => z0.2.2) := fun x y _ => Subsingleton.elim x y
    refine ⟨(Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
          (∀ x : Fin 1, p.1 ((fun _ : Fin 1 => z0.2.1) x) = z0.1.1 ((fun _ : Fin 1 => z0.2.1) x)) ∧
          ∀ y : Fin 1, p.2 ((fun _ : Fin 1 => z0.2.2) y) = z0.1.2 ((fun _ : Fin 1 => z0.2.2) y)))
          ×ˢ {z0.2}, ?_, ?_⟩
    · intro z _ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      obtain ⟨e1a, e1b⟩ := pos_inj e1
      obtain ⟨e2a, e2b⟩ := pos_inj e2
      rw [e1a] at e1b
      rw [e2a] at e2b
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨⟨fun _ => e1b, fun _ => e2b⟩, Prod.ext e1a e2a⟩
    · rw [Finset.card_product, Finset.card_singleton, mul_one]
      exact (constr_card _ hinj _ hinj' z0.1).le

theorem copies_le {k₀ l₀ n q : ℕ} (R : BMat k₀ l₀) (B : BMat (n * q) (n * q)) :
    (Finset.univ.filter (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) ×
        ((Fin k₀ → Fin n) × (Fin l₀ → Fin n)) =>
       IsCopy R (pick B z.1) z.2.1 z.2.2)).card * q ^ (k₀ + l₀) ≤
      q ^ n * q ^ n * copyCount R B := by
  unfold copyCount
  apply card_mul_le' _ _ (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) ×
        ((Fin k₀ → Fin n) × (Fin l₀ → Fin n)) =>
    ((fun a => pos (z.2.1 a) (z.1.1 (z.2.1 a))), (fun b => pos (z.2.2 b) (z.1.2 (z.2.2 b)))))
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨fun a a' h => pos_lt _ _ (h1 h), fun b b' h => pos_lt _ _ (h2 h), fun a b => h3 a b⟩
  · intro z0 hz0
    have hc0 := (Finset.mem_filter.mp hz0).2
    have hinj : Function.Injective z0.2.1 := hc0.1.injective
    have hinj' : Function.Injective z0.2.2 := hc0.2.1.injective
    refine ⟨(Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
          (∀ x, p.1 (z0.2.1 x) = z0.1.1 (z0.2.1 x)) ∧ ∀ y, p.2 (z0.2.2 y) = z0.1.2 (z0.2.2 y)))
          ×ˢ {z0.2}, ?_, ?_⟩
    · intro z _ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      have e1' := fun a => pos_inj (congrFun e1 a)
      have e2' := fun b => pos_inj (congrFun e2 b)
      have hr : z.2.1 = z0.2.1 := funext fun a => (e1' a).1
      have hc : z.2.2 = z0.2.2 := funext fun b => (e2' b).1
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨⟨fun a => ?_, fun b => ?_⟩, Prod.ext hr hc⟩
      · have := (e1' a).2; rw [hr] at this; exact this
      · have := (e2' b).2; rw [hc] at this; exact this
    · rw [Finset.card_product, Finset.card_singleton, mul_one]
      exact (constr_card _ hinj _ hinj' z0.1).le

end Fact2bAux

open Fact2bAux in
/-- Fact 2(b): for some `q`, every matrix within `q² D_R(A) / 2` of `A^(q)` contains `H`. -/
theorem fact2b {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    {n : ℕ} (A : BMat n n) (hn : 0 < n) :
    ∃ q, 0 < q ∧ ∀ B' : BMat (n * q) (n * q),
      2 * hamming (hostBlowup A q) B' < q ^ 2 * editDist R A → Contains H B' := by
  obtain ⟨K, -, hK⟩ := infl_density hI
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hne : (1:ℝ) ≤ (n:ℝ) ^ (k₀ + l₀) := one_le_pow₀ hnR
  set d : ℝ := 1 / (2 * (n:ℝ) ^ (k₀ + l₀)) with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d ≤ 1 := by
    rw [hd, div_le_one (by positivity)]; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈2 * (4 / d) ^ K⌉₊ + 1 := ⟨_, rfl⟩
  have hq0 : 0 < q := by omega
  refine ⟨q, hq0, ?_⟩
  intro B hB
  set D := editDist R A with hDdef
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, mul_zero] at hB; exact absurd hB (Nat.not_lt_zero _)
    · exact h
  have hcardP : (Finset.univ : Finset ((Fin n → Fin q) × (Fin n → Fin q))).card = q ^ n * q ^ n := by
    simp [Finset.card_univ, Fintype.card_prod]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ((Fin n → Fin q) × (Fin n → Fin q))))
    (fun p => D ≤ hamming A (pick B p))
  rw [hcardP] at hsplit
  set bad := Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
    D ≤ hamming A (pick B p)) with hbad
  set good := Finset.univ.filter (fun p : (Fin n → Fin q) × (Fin n → Fin q) =>
    ¬ D ≤ hamming A (pick B p)) with hgood
  have hmarkov : bad.card * D ≤ ∑ p : (Fin n → Fin q) × (Fin n → Fin q), hamming A (pick B p) := by
    calc bad.card * D = ∑ _p ∈ bad, D := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ bad, hamming A (pick B p) :=
          Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p : (Fin n → Fin q) × (Fin n → Fin q), hamming A (pick B p) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have havg := averaging A B
  have h2bad : 2 * bad.card < q ^ n * q ^ n := by
    have h1 : bad.card * D * q ^ (1 + 1) * 2 ≤
        q ^ n * q ^ n * (2 * hamming (hostBlowup A q) B) := by
      calc bad.card * D * q ^ (1 + 1) * 2
          ≤ (∑ p : (Fin n → Fin q) × (Fin n → Fin q), hamming A (pick B p)) * q ^ (1 + 1) * 2 := by
            gcongr
        _ ≤ q ^ n * q ^ n * hamming (hostBlowup A q) B * 2 := by gcongr
        _ = _ := by ring
    have h2 : q ^ n * q ^ n * (2 * hamming (hostBlowup A q) B) < q ^ n * q ^ n * (q ^ 2 * D) :=
      Nat.mul_lt_mul_of_pos_left hB (by positivity)
    have h3 : (2 * bad.card) * (D * q ^ 2) < (q ^ n * q ^ n) * (D * q ^ 2) := by
      calc (2 * bad.card) * (D * q ^ 2) = bad.card * D * q ^ (1 + 1) * 2 := by ring
        _ < q ^ n * q ^ n * (q ^ 2 * D) := lt_of_le_of_lt h1 h2
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_right h3
  have hgood2 : q ^ n * q ^ n < 2 * good.card := by omega
  have hgS : good.card ≤ (Finset.univ.filter (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) ×
        ((Fin k₀ → Fin n) × (Fin l₀ → Fin n)) =>
       IsCopy R (pick B z.1) z.2.1 z.2.2)).card := by
    refine le_trans (Finset.card_le_card (t := Finset.image Prod.fst _) ?_)
      (Finset.card_image_le (f := Prod.fst))
    intro p hp
    simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hp
    have hc : Contains R (pick B p) := by
      by_contra hf
      exact absurd (editDist_le R A (pick B p) hf) (not_le.mpr hp)
    obtain ⟨r, c, hrc⟩ := hc
    exact Finset.mem_image.mpr ⟨(p, (r, c)), by simp [hrc], rfl⟩
  have hSN := copies_le (n := n) (q := q) R B
  have hN : q ^ (k₀ + l₀) < 2 * copyCount R B := by
    have h4 : q ^ n * q ^ n * q ^ (k₀ + l₀) < q ^ n * q ^ n * (2 * copyCount R B) := by
      calc q ^ n * q ^ n * q ^ (k₀ + l₀) < 2 * good.card * q ^ (k₀ + l₀) :=
            Nat.mul_lt_mul_of_pos_right hgood2 (by positivity)
        _ ≤ 2 * (Finset.univ.filter (fun z : ((Fin n → Fin q) × (Fin n → Fin q)) ×
              ((Fin k₀ → Fin n) × (Fin l₀ → Fin n)) =>
             IsCopy R (pick B z.1) z.2.1 z.2.2)).card * q ^ (k₀ + l₀) := by gcongr
        _ ≤ 2 * (q ^ n * q ^ n * copyCount R B) := by rw [mul_assoc]; gcongr
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_left h4
  have hNR : (q : ℝ) ^ (k₀ + l₀) ≤ 2 * (copyCount R B : ℝ) := by exact_mod_cast hN.le
  have hdens : d * ((n * q : ℕ) : ℝ) ^ (k₀ + l₀) ≤ copyCount R B := by
    have : d * ((n * q : ℕ) : ℝ) ^ (k₀ + l₀) = (q : ℝ) ^ (k₀ + l₀) / 2 := by
      rw [hd, Nat.cast_mul, mul_pow]; field_simp
    rw [this]; linarith
  have hsize : 2 * (4 / d) ^ K ≤ ((n * q : ℕ) : ℝ) := by
    have h1 : 2 * (4 / d) ^ K ≤ (⌈2 * (4 / d) ^ K⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (q : ℝ) = (⌈2 * (4 / d) ^ K⌉₊ : ℝ) + 1 := by rw [hq]; push_cast; ring
    have h3 : (0 : ℝ) ≤ (⌈2 * (4 / d) ^ K⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [Nat.cast_mul, h2]
    nlinarith
  have hH := hK (n * q) B d hd0 hd1 hdens hsize
  have hnq : (0 : ℝ) < ((n * q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hn hq0
  have hpos : 0 < (d / 4) ^ K * ((n * q : ℕ) : ℝ) ^ (k + l) := by positivity
  have hne0 : copyCount H B ≠ 0 := by
    intro h; rw [h, Nat.cast_zero] at hH; linarith
  by_contra hc
  exact hne0 ((copyCount_eq_zero_iff H B).mpr hc)

end OrderedRemoval
