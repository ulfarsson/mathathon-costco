/-
`Infl R H` as monotone surjections, containment, and Fact 2(a).
-/
import OrderedRemoval.Dup.Defs

namespace OrderedRemoval

open Classical

theorem dupIdx_monotone {l : ℕ} (j : Fin l) : Monotone (dupIdx j) := by
  intro a b hab
  have h : a.val ≤ b.val := hab
  show (dupIdx j a).val ≤ (dupIdx j b).val
  simp only [dupIdx_val]
  split_ifs <;> omega

theorem dupIdx_surjective {l : ℕ} (j : Fin l) : Function.Surjective (dupIdx j) := by
  intro y
  have := y.isLt
  by_cases h : y.val ≤ j.val
  · exact ⟨⟨y.val, by omega⟩, Fin.ext (by simp only [dupIdx_val]; split_ifs; omega)⟩
  · exact ⟨⟨y.val + 1, by omega⟩, Fin.ext (by simp only [dupIdx_val]; split_ifs <;> omega)⟩

/-- `H` is `R` read along monotone surjections of the rows and the columns. -/
theorem infl_repr {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H) :
    ∃ σ : Fin k → Fin k₀, ∃ τ : Fin l → Fin l₀, Monotone σ ∧ Monotone τ ∧
      Function.Surjective σ ∧ Function.Surjective τ ∧ ∀ a b, H a b = R (σ a) (τ b) := by
  induction hI with
  | refl R =>
    exact ⟨id, id, monotone_id, monotone_id, Function.surjective_id, Function.surjective_id,
      fun _ _ => rfl⟩
  | col j _ ih =>
    obtain ⟨σ, τ, hσ, hτ, hσs, hτs, h⟩ := ih
    exact ⟨σ, τ ∘ dupIdx j, hσ, hτ.comp (dupIdx_monotone j), hσs,
      hτs.comp (dupIdx_surjective j), fun a b => h a (dupIdx j b)⟩
  | row i _ ih =>
    obtain ⟨σ, τ, hσ, hτ, hσs, hτs, h⟩ := ih
    exact ⟨σ ∘ dupIdx i, τ, hσ.comp (dupIdx_monotone i), hτ,
      hσs.comp (dupIdx_surjective i), hτs, fun a b => h (dupIdx i a) b⟩

namespace ReprAux

theorem sec_strictMono {k k₀ : ℕ} {σ : Fin k → Fin k₀} (hσ : Monotone σ)
    (hs : Function.Surjective σ) : StrictMono (Function.surjInv hs) := by
  intro a a' h
  by_contra h'
  have := hσ (not_lt.mp h')
  rw [Function.surjInv_eq hs, Function.surjInv_eq hs] at this
  exact absurd h (not_lt.mpr this)

end ReprAux

/-- `H` contains `R`: a copy of `H` gives a copy of `R`. -/
theorem infl_contains {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    {n m : ℕ} (B : BMat n m) : Contains H B → Contains R B := by
  obtain ⟨σ, τ, hσ, hτ, hσs, hτs, h⟩ := infl_repr hI
  rintro ⟨r, c, hr, hc, hrc⟩
  refine ⟨r ∘ Function.surjInv hσs, c ∘ Function.surjInv hτs,
    hr.comp (ReprAux.sec_strictMono hσ hσs), hc.comp (ReprAux.sec_strictMono hτ hτs),
    fun a b => ?_⟩
  simp only [Function.comp]
  rw [hrc, h, Function.surjInv_eq hσs, Function.surjInv_eq hτs]

theorem infl_pos {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) : 0 < k ∧ 0 < l := by
  obtain ⟨σ, τ, -, -, hσs, hτs, -⟩ := infl_repr hI
  obtain ⟨a, -⟩ := hσs ⟨0, hk₀⟩
  obtain ⟨b, -⟩ := hτs ⟨0, hl₀⟩
  exact ⟨a.pos, b.pos⟩

/-- Every `R`-free matrix is `H`-free, so `D_H(A) ≤ D_R(A)`. -/
theorem editDist_le_of_infl {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) {n m : ℕ} (A : BMat n m) :
    editDist H A ≤ editDist R A := by
  obtain ⟨B, hB, hAB⟩ := editDist_spec R A (exists_free R hk₀ hl₀ n m)
  rw [← hAB]
  exact editDist_le H A B (fun hc => hB (infl_contains hI B hc))

/-- Counting functions with prescribed sets on an injective family of positions. -/
theorem card_constrained {a b : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (s : Fin a → Fin b) (hs : Function.Injective s) (T : Fin a → Finset X) (t : ℕ)
    (hT : ∀ x, (T x).card = t) :
    (Finset.univ.filter (fun f : Fin b → X => ∀ x, f (s x) ∈ T x)).card * Fintype.card X ^ a =
      t ^ a * Fintype.card X ^ b := by
  let p : Fin b → Prop := fun i => ∃ x, s x = i
  let S : Fin b → Finset X := fun i => if h : p i then T h.choose else Finset.univ
  have hfilt : Finset.univ.filter (fun f : Fin b → X => ∀ x, f (s x) ∈ T x) =
      Fintype.piFinset S := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hf i
      by_cases h : p i
      · simp only [S, h, dite_eq_left]
        have := hf h.choose
        rwa [h.choose_spec] at this
      · simp only [S, h, dite_eq_right, not_false_eq_true, Finset.mem_univ]
    · intro hf x
      have hx := hf (s x)
      have h : p (s x) := ⟨x, rfl⟩
      simp only [S, h, dite_eq_left] at hx
      have e : h.choose = x := hs h.choose_spec
      rwa [e] at hx
  have hcardS : ∀ i, (S i).card = if p i then t else Fintype.card X := by
    intro i
    by_cases h : p i
    · simp only [S, h, dite_eq_left, ite_true, hT]
    · simp only [S, h, dite_eq_right, ite_false, not_false_eq_true, Finset.card_univ]
  have himg : (Finset.univ.filter p).card = a := by
    have : Finset.univ.filter p = Finset.univ.image s := by
      ext i
      simp [p, Finset.mem_image]
    rw [this, Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin]
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  rw [Finset.card_univ, Fintype.card_fin, himg] at hsum
  rw [hfilt, Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hcardS i),
    Finset.prod_ite, Finset.prod_const, Finset.prod_const, himg]
  conv_rhs => rw [← hsum, pow_add]
  ring

namespace ReprAux

theorem strictMono_of_succ {m : ℕ} {β : Type} [Preorder β] (f : Fin m → β)
    (h : ∀ a a' : Fin m, a'.val = a.val + 1 → f a < f a') : StrictMono f := by
  suffices H : ∀ d : ℕ, ∀ a b : Fin m, b.val = a.val + d + 1 → f a < f b by
    intro a b hab
    have : a.val < b.val := hab
    exact H (b.val - a.val - 1) a b (by omega)
  intro d
  induction d with
  | zero => intro a b hb; exact h a b (by omega)
  | succ d ih =>
    intro a b hb
    have hc : a.val + d + 1 < m := by have := b.isLt; omega
    exact lt_trans (ih a ⟨a.val + d + 1, hc⟩ rfl) (h _ b (by simp only; omega))

theorem block_card {n q : ℕ} (hq : 0 < q) (m : Fin n) :
    (Finset.univ.filter (fun y : Fin (n * q) => y.val / q = m.val)).card = q := by
  have hm := m.isLt
  have hmq : m.val * q + q ≤ n * q := by
    have : (m.val + 1) * q ≤ n * q := Nat.mul_le_mul_right q hm
    linarith [this]
  conv_rhs => rw [← Finset.card_fin q]
  refine Finset.card_nbij' (fun y => ⟨y.val % q, Nat.mod_lt _ hq⟩)
    (fun i => ⟨m.val * q + i.val, by have := i.isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro y _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro i _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have := i.isLt
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt this, Nat.zero_add]
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    apply Fin.ext
    simp only
    rw [← hy, Nat.mul_comm]
    exact Nat.div_add_mod y.val q
  · intro i _
    apply Fin.ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

theorem fiber_card {n q k a : ℕ} (hq : 0 < q) (s : Fin a → Fin k) (hs : Function.Injective s)
    (ρ : Fin a → Fin n) :
    (Finset.univ.filter (fun r : Fin k → Fin (n * q) => ∀ x, (r (s x)).val / q = (ρ x).val)).card
      * n ^ a = (n * q) ^ k := by
  have h := card_constrained s hs
    (fun x => Finset.univ.filter (fun y : Fin (n * q) => y.val / q = (ρ x).val)) q
    (fun x => block_card hq (ρ x))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.card_fin] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hq a)
  calc _ = _ * (n * q) ^ a := by rw [mul_pow, mul_assoc]
    _ = q ^ a * (n * q) ^ k := h
    _ = _ := mul_comm _ _

end ReprAux

/-- Fact 2(a): `N_H(A^(q)) / (qn)^(k+l) ≤ N_R(A) / n^(k₀+l₀)`. -/
theorem fact2a {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    (hR : Reduced R) {n : ℕ} (A : BMat n n) (q : ℕ) (hq : 0 < q) :
    copyCount H (hostBlowup A q) * n ^ (k₀ + l₀) ≤ copyCount R A * (n * q) ^ (k + l) := by
  obtain ⟨σ, τ, hσ, hτ, hσs, hτs, hH⟩ := infl_repr hI
  have hs := ReprAux.sec_strictMono hσ hσs
  have ht := ReprAux.sec_strictMono hτ hτs
  have hσs' : ∀ a, σ (Function.surjInv hσs a) = a := Function.surjInv_eq hσs
  have hτs' : ∀ b, τ (Function.surjInv hτs b) = b := Function.surjInv_eq hτs
  set s := Function.surjInv hσs
  set t := Function.surjInv hτs
  let φ : (Fin k → Fin (n * q)) × (Fin l → Fin (n * q)) → (Fin k₀ → Fin n) × (Fin l₀ → Fin n) :=
    fun rc => (fun a => ⟨(rc.1 (s a)).val / q, div_lt_of_lt_mul' _⟩,
      fun b => ⟨(rc.2 (t b)).val / q, div_lt_of_lt_mul' _⟩)
  have hmap : ∀ rc : (Fin k → Fin (n * q)) × (Fin l → Fin (n * q)),
      IsCopy H (hostBlowup A q) rc.1 rc.2 → IsCopy R A (φ rc).1 (φ rc).2 := by
    rintro ⟨r, c⟩ ⟨hr, hc, hrc⟩
    refine ⟨?_, ?_, ?_⟩
    · apply ReprAux.strictMono_of_succ
      intro a a' haa'
      have hlt : r (s a) < r (s a') := hr (hs (by rw [Fin.lt_def]; omega))
      have hle : (r (s a)).val / q ≤ (r (s a')).val / q :=
        Nat.div_le_div_right (le_of_lt hlt)
      rw [Fin.lt_def]
      show (r (s a)).val / q < (r (s a')).val / q
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        obtain ⟨b, hb⟩ := hR.1 a a' haa'
        obtain ⟨j', rfl⟩ := hτs b
        apply hb
        have e1 : R a (τ j') = H (s a) j' := by rw [hH, hσs']
        have e2 : R a' (τ j') = H (s a') j' := by rw [hH, hσs']
        rw [e1, e2, ← hrc, ← hrc]
        simp only [hostBlowup]
        congr 1
        exact Fin.ext h
    · apply ReprAux.strictMono_of_succ
      intro b b' hbb'
      have hlt : c (t b) < c (t b') := hc (ht (by rw [Fin.lt_def]; omega))
      have hle : (c (t b)).val / q ≤ (c (t b')).val / q :=
        Nat.div_le_div_right (le_of_lt hlt)
      rw [Fin.lt_def]
      show (c (t b)).val / q < (c (t b')).val / q
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha⟩ := hR.2 b b' hbb'
        obtain ⟨i', rfl⟩ := hσs a
        apply ha
        have e1 : R (σ i') b = H i' (t b) := by rw [hH, hτs']
        have e2 : R (σ i') b' = H i' (t b') := by rw [hH, hτs']
        rw [e1, e2, ← hrc, ← hrc]
        simp only [hostBlowup]
        congr 1
        exact Fin.ext h
    · intro a b
      have e := hrc (s a) (t b)
      simp only [hostBlowup] at e
      exact e.trans (by rw [hH, hσs', hτs'])
  unfold copyCount
  rw [Finset.card_eq_sum_card_fiberwise (f := φ)
    (t := Finset.univ.filter (fun rc : (Fin k₀ → Fin n) × (Fin l₀ → Fin n) =>
      IsCopy R A rc.1 rc.2)) (by
        intro rc hrc
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hrc ⊢
        exact hmap rc hrc), Finset.sum_mul]
  calc _ ≤ ∑ y ∈ Finset.univ.filter (fun rc : (Fin k₀ → Fin n) × (Fin l₀ → Fin n) =>
          IsCopy R A rc.1 rc.2), (n * q) ^ (k + l) := by
        apply Finset.sum_le_sum
        intro y _
        let Fr := Finset.univ.filter
          (fun r : Fin k → Fin (n * q) => ∀ x, (r (s x)).val / q = (y.1 x).val)
        let Fc := Finset.univ.filter
          (fun c : Fin l → Fin (n * q) => ∀ x, (c (t x)).val / q = (y.2 x).val)
        have hsub : (Finset.univ.filter
            (fun rc : (Fin k → Fin (n * q)) × (Fin l → Fin (n * q)) =>
              IsCopy H (hostBlowup A q) rc.1 rc.2)).filter (fun rc => φ rc = y) ⊆ Fr ×ˢ Fc := by
          intro rc hrc
          obtain ⟨-, hφ⟩ := Finset.mem_filter.mp hrc
          subst hφ
          exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => rfl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => rfl⟩⟩
        have h1 := ReprAux.fiber_card hq s hs.injective y.1
        have h2 := ReprAux.fiber_card hq t ht.injective y.2
        calc _ ≤ (Fr ×ˢ Fc).card * n ^ (k₀ + l₀) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
          _ = (Fr.card * n ^ k₀) * (Fc.card * n ^ l₀) := by
              rw [Finset.card_product, pow_add]; ring
          _ = (n * q) ^ (k + l) := by rw [h1, h2, pow_add]
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

end OrderedRemoval
