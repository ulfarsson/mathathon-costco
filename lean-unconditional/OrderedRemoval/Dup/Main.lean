/-
The duplication theorem: repeating rows and columns does not change whether a pattern
satisfies the conjecture.
-/
import OrderedRemoval.Dup.Fact2b

namespace OrderedRemoval

open Classical

/-- If `R` satisfies the conjecture, so does every `H` obtained from it by repeating rows and
columns (Fact 1). -/
theorem polyRemoval_of_infl {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l} (hI : Infl R H)
    (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) : PolyRemoval R → PolyRemoval H := by
  rintro ⟨c, C, hc, hC, hR⟩
  obtain ⟨hk, hl⟩ := infl_pos hI hk₀ hl₀
  obtain ⟨K, hK1, hKd⟩ := infl_density hI
  have hc₁pos : 0 < min c 1 := lt_min hc one_pos
  have hc₁le : min c 1 ≤ c := min_le_left _ _
  have hc₁1 : min c 1 ≤ 1 := min_le_right _ _
  set c₁ := min c 1 with hc₁
  have hKe : 0 < K * (k + l) := Nat.mul_pos (by omega) (by omega)
  refine ⟨min ((c₁ / 4) ^ K) (1 / (2 ^ (k + l) * (4 / c₁) ^ (K * (k + l)))),
    C * ((K * (k + l) : ℕ) : ℝ), lt_min (by positivity) (by positivity),
    mul_pos hC (by exact_mod_cast hKe), ?_⟩
  intro n A ε hε hε1 hD
  have hx0 : 0 < ε ^ C := Real.rpow_pos_of_pos hε C
  have hx1 : ε ^ C ≤ 1 := Real.rpow_le_one hε.le hε1 hC.le
  rw [Real.rpow_mul_natCast hε.le C (K * (k + l))]
  set x := ε ^ C with hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, zero_pow (by omega), mul_zero]; positivity
  have hDR : ε * (n : ℝ) ^ 2 ≤ (editDist R A : ℝ) :=
    hD.trans (by exact_mod_cast editDist_le_of_infl hI hk₀ hl₀ A)
  have hNR := hR n A ε hε hε1 hDR
  have hd0 : 0 < c₁ * x := mul_pos hc₁pos hx0
  have hd1 : c₁ * x ≤ 1 := by nlinarith
  have hdN : c₁ * x * (n : ℝ) ^ (k₀ + l₀) ≤ copyCount R A := by
    refine le_trans ?_ hNR
    have : (0 : ℝ) ≤ x * (n : ℝ) ^ (k₀ + l₀) := by positivity
    nlinarith
  have hNH1 : (1 : ℝ) ≤ copyCount H A := by
    have hDpos : 0 < editDist H A := by
      have h0 : (0 : ℝ) < ε * (n : ℝ) ^ 2 := by positivity
      exact_mod_cast h0.trans_le hD
    have hnotfree : ¬ Free H A := fun hf => by
      have := (editDist_eq_zero_iff H A (exists_free H hk hl n n)).2 hf
      omega
    have h0 : copyCount H A ≠ 0 := fun h0 => hnotfree ((copyCount_eq_zero_iff H A).1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  by_cases hbig : 2 * (4 / (c₁ * x)) ^ K ≤ (n : ℝ)
  · have h := hKd n A (c₁ * x) hd0 hd1 hdN hbig
    have hxK : x ^ (K * (k + l)) ≤ x ^ K :=
      pow_le_pow_of_le_one hx0.le hx1 (Nat.le_mul_of_pos_right K (by omega))
    calc min ((c₁ / 4) ^ K) (1 / (2 ^ (k + l) * (4 / c₁) ^ (K * (k + l)))) * x ^ (K * (k + l)) *
          (n : ℝ) ^ (k + l)
        ≤ (c₁ / 4) ^ K * x ^ K * (n : ℝ) ^ (k + l) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (min_le_left _ _) hxK (by positivity) (by positivity)) (by positivity)
      _ = (c₁ * x / 4) ^ K * (n : ℝ) ^ (k + l) := by
          rw [show c₁ * x / 4 = c₁ / 4 * x by ring, mul_pow]
      _ ≤ _ := h
  · rw [not_le] at hbig
    have hxy : x * (4 / (c₁ * x)) = 4 / c₁ := by field_simp
    have hn' : (n : ℝ) ^ (k + l) ≤ (2 * (4 / (c₁ * x)) ^ K) ^ (k + l) :=
      pow_le_pow_left₀ (by positivity) hbig.le _
    calc min ((c₁ / 4) ^ K) (1 / (2 ^ (k + l) * (4 / c₁) ^ (K * (k + l)))) * x ^ (K * (k + l)) *
          (n : ℝ) ^ (k + l)
        ≤ (1 / (2 ^ (k + l) * (4 / c₁) ^ (K * (k + l)))) * x ^ (K * (k + l)) *
          (2 * (4 / (c₁ * x)) ^ K) ^ (k + l) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)) hn'
            (by positivity) (by positivity)
      _ = (1 / (2 ^ (k + l) * (4 / c₁) ^ (K * (k + l)))) *
          (2 ^ (k + l) * (x * (4 / (c₁ * x))) ^ (K * (k + l))) := by
          rw [mul_pow, ← pow_mul, mul_pow (x)]; ring
      _ = 1 := by rw [hxy]; field_simp
      _ ≤ _ := hNH1

/-- If `H` satisfies the conjecture, so does the reduced pattern `R` it comes from (Fact 2). -/
theorem polyRemoval_of_infl_reduced {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l}
    (hI : Infl R H) (hR : Reduced R) (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) :
    PolyRemoval H → PolyRemoval R := by
  rintro ⟨c, C, hc, hC, hH⟩
  obtain ⟨hk, hl⟩ := infl_pos hI hk₀ hl₀
  refine ⟨c * (1 / 2 : ℝ) ^ C, C, by positivity, hC, ?_⟩
  intro n A ε hε hε1 hD
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, zero_pow (by omega), mul_zero]; positivity
  obtain ⟨q, hq, hB⟩ := fact2b hI A hn
  obtain ⟨B', hB'free, hB'd⟩ := editDist_spec H (hostBlowup A q) (exists_free H hk hl (n * q) (n * q))
  have hle : q ^ 2 * editDist R A ≤ 2 * editDist H (hostBlowup A q) := by
    by_contra hlt
    rw [not_le] at hlt
    exact hB'free (hB B' (by rw [hB'd]; exact hlt))
  have hDH : ε / 2 * ((n * q : ℕ) : ℝ) ^ 2 ≤ (editDist H (hostBlowup A q) : ℝ) := by
    have h1 : ((q ^ 2 * editDist R A : ℕ) : ℝ) ≤ ((2 * editDist H (hostBlowup A q) : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at h1 ⊢
    have hq' : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD hq']
  have h2 := hH (n * q) (hostBlowup A q) (ε / 2) (by positivity) (by linarith) hDH
  have h3 : (copyCount H (hostBlowup A q) : ℝ) * (n : ℝ) ^ (k₀ + l₀) ≤
      (copyCount R A : ℝ) * ((n * q : ℕ) : ℝ) ^ (k + l) := by
    exact_mod_cast fact2a hI hR A q hq
  have hpos : (0 : ℝ) < ((n * q : ℕ) : ℝ) ^ (k + l) := by
    have : 0 < n * q := Nat.mul_pos hn hq
    positivity
  have hε2 : (ε / 2) ^ C = ε ^ C * (1 / 2 : ℝ) ^ C := by
    rw [div_eq_mul_one_div ε 2, Real.mul_rpow hε.le (by norm_num)]
  have hnr : (0 : ℝ) ≤ (n : ℝ) ^ (k₀ + l₀) := by positivity
  have key : c * (1 / 2 : ℝ) ^ C * ε ^ C * (n : ℝ) ^ (k₀ + l₀) * ((n * q : ℕ) : ℝ) ^ (k + l) ≤
      (copyCount R A : ℝ) * ((n * q : ℕ) : ℝ) ^ (k + l) := by
    calc c * (1 / 2 : ℝ) ^ C * ε ^ C * (n : ℝ) ^ (k₀ + l₀) * ((n * q : ℕ) : ℝ) ^ (k + l)
        = (c * (ε / 2) ^ C * ((n * q : ℕ) : ℝ) ^ (k + l)) * (n : ℝ) ^ (k₀ + l₀) := by
          rw [hε2]; ring
      _ ≤ (copyCount H (hostBlowup A q) : ℝ) * (n : ℝ) ^ (k₀ + l₀) :=
          mul_le_mul_of_nonneg_right h2 hnr
      _ ≤ _ := h3
  exact le_of_mul_le_mul_right key hpos

/-- **Duplication theorem.** If `H` is obtained from a reduced pattern `R` by repeating rows and
columns, then `H` satisfies the conjecture if and only if `R` does. -/
theorem polyRemoval_iff_of_infl {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l}
    (hI : Infl R H) (hR : Reduced R) (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) :
    PolyRemoval H ↔ PolyRemoval R :=
  ⟨polyRemoval_of_infl_reduced hI hR hk₀ hl₀, polyRemoval_of_infl hI hk₀ hl₀⟩

/-- A reduced counterexample stays a counterexample after repeating rows and columns. -/
theorem not_polyRemoval_of_infl {k₀ l₀ k l : ℕ} {R : BMat k₀ l₀} {H : BMat k l}
    (hI : Infl R H) (hR : Reduced R) (hk₀ : 0 < k₀) (hl₀ : 0 < l₀) (h : ¬ PolyRemoval R) :
    ¬ PolyRemoval H :=
  fun hH => h ((polyRemoval_iff_of_infl hI hR hk₀ hl₀).1 hH)

end OrderedRemoval
