import OrderedRemoval.Statements
import OAI.Combinatorics.MatrixRemoval.Main

namespace OrderedRemoval

open OAI.Problem348

theorem oai_hamming_eq {n : ℕ} (A B : BMat n n) :
    hammingDistance (A : BinaryMatrix n) (B : BinaryMatrix n) = hamming A B := rfl

theorem oai_copyCount_eq {k n : ℕ} (H : BMat k k) (A : BMat n n) :
    OAI.Problem348.copyCount (H : BinaryMatrix k) (A : BinaryMatrix n) = copyCount H A := by
  unfold OAI.Problem348.copyCount OAI.Problem348.orderedCopies copyCount IsCopy
  simp only [← Fintype.card_subtype]
  let e : {rc : (Fin k → Fin n) × (Fin k → Fin n) //
        StrictMono rc.1 ∧ StrictMono rc.2 ∧ ∀ i j, A (rc.1 i) (rc.2 j) = H i j} ≃
      {rc : IncreasingMap k n × IncreasingMap k n //
        ∀ i j, A (rc.1.val i) (rc.2.val j) = H i j} :=
  { toFun := fun ⟨⟨r, c⟩, hr, hc, hcopy⟩ => ⟨⟨⟨r, hr⟩, ⟨c, hc⟩⟩, hcopy⟩
    invFun := fun ⟨⟨⟨r, hr⟩, ⟨c, hc⟩⟩, hcopy⟩ => ⟨⟨r, c⟩, hr, hc, hcopy⟩
    left_inv := by intro ⟨⟨r, c⟩, hr, hc, hcopy⟩; rfl
    right_inv := by intro ⟨⟨⟨r, hr⟩, ⟨c, hc⟩⟩, hcopy⟩; rfl }
  exact (Fintype.card_congr e).symm

theorem oai_HFree_iff {n : ℕ} (A : BMat n n) :
    HFree (fixedH : BinaryMatrix 66) (A : BinaryMatrix n) ↔
      Free (fixedH : BMat 66 66) A := by
  unfold HFree
  rw [oai_copyCount_eq (H := (fixedH : BMat 66 66)) (A := A)]
  rw [copyCount_eq_zero_iff]

theorem oai_noZeroLine : NoZeroLine (fixedH : BMat 66 66) := by
  constructor
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

theorem oai_fixedMinEdits_eq_editDist {n : ℕ} (A : BMat n n) :
    (fixedMinEdits (A : BinaryMatrix n) : ℕ) = editDist (fixedH : BMat 66 66) A := by
  classical
  have hF1 : ∃ i j, (fixedH : BMat 66 66) i j = true := by
    obtain ⟨j, hj⟩ := oai_noZeroLine.1 (0 : Fin 66)
    exact ⟨0, j, hj⟩
  have hfree : ∃ B : BMat n n, Free (fixedH : BMat 66 66) B :=
    exists_free (fixedH : BMat 66 66) (by norm_num) (by norm_num) n n
  obtain ⟨B₀, hB₀free, hB₀ham⟩ := editDist_spec (fixedH : BMat 66 66) A hfree
  have hne : (Finset.univ.image (fun B : BMat n n =>
      if HFree fixedH B then hammingDistance A B else n * n + 1)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨A, Finset.mem_univ _, rfl⟩⟩
  have hfix : fixedMinEdits A =
      (Finset.univ.image (fun B : BMat n n =>
        if HFree fixedH B then hammingDistance A B else n * n + 1)).min' hne := rfl
  have hmin : fixedMinEdits A ≤ editDist (fixedH : BMat 66 66) A := by
    rw [hfix]
    refine Finset.min'_le _ _ (Finset.mem_image.mpr ⟨B₀, Finset.mem_univ _, ?_⟩)
    rw [ite_eq_left ((oai_HFree_iff B₀).mpr hB₀free), oai_hamming_eq, hB₀ham]
  refine le_antisymm hmin ?_
  rw [hfix]
  obtain ⟨B₁, -, hB₁⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  rcases em (HFree fixedH B₁) with h | h
  · rw [ite_eq_left h] at hB₁
    rw [← hB₁, oai_hamming_eq]
    exact editDist_le (fixedH : BMat 66 66) A B₁ ((oai_HFree_iff B₁).mp h)
  · rw [ite_eq_right h] at hB₁
    have hge : n * n + 1 ≤ editDist (fixedH : BMat 66 66) A := by
      rw [hB₁, ← hfix]
      exact hmin
    have hcard : editDist (fixedH : BMat 66 66) A ≤ n * n :=
      editDist_le_card (fixedH : BMat 66 66) A hF1
    omega

theorem oai_not_polyRemoval : ¬ PolyRemoval (fixedH : BMat 66 66) := by
  intro hPoly
  obtain ⟨c, C, hc, hC, hMain⟩ := hPoly
  have hOAI := OAI.Problem348.no_polynomial_removal_bound c C hc hC
  obtain ⟨n, hn, ε, hε0, hε1, A, hDist, hCopy⟩ := hOAI
  have hε_le1 : ε ≤ 1 := le_of_lt hε1
  have hDist' : ε * (n : ℝ) ^ 2 ≤ (editDist (fixedH : BMat 66 66) (A : BMat n n) : ℝ) := by
    have hFixedNat : (fixedMinEdits (A : BinaryMatrix n) : ℕ) = editDist (fixedH : BMat 66 66) (A : BMat n n) := oai_fixedMinEdits_eq_editDist (A := (A : BMat n n))
    have hFixed : (fixedMinEdits (A : BinaryMatrix n) : ℝ) = (editDist (fixedH : BMat 66 66) (A : BMat n n) : ℝ) := by exact_mod_cast hFixedNat
    have hDistReal : (fixedDistance (A : BinaryMatrix n) : ℝ) ≥ ε := hDist
    unfold fixedDistance at hDistReal
    have h1 : (fixedMinEdits (A : BinaryMatrix n) : ℝ) ≥ ε * (n : ℝ) ^ 2 := by
      have h2 : (fixedMinEdits (A : BinaryMatrix n) : ℝ) / (n : ℝ) ^ 2 ≥ ε := hDistReal
      have h3 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h4 : ε * (n : ℝ) ^ 2 ≤ (fixedMinEdits (A : BinaryMatrix n) : ℝ) := by
        have h5 : ε ≤ (fixedMinEdits (A : BinaryMatrix n) : ℝ) / (n : ℝ) ^ 2 := hDistReal
        have h6 : ε * (n : ℝ) ^ 2 ≤ ((fixedMinEdits (A : BinaryMatrix n) : ℝ) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right h5 (le_of_lt h3)
        have h7 : ((fixedMinEdits (A : BinaryMatrix n) : ℝ) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 = (fixedMinEdits (A : BinaryMatrix n) : ℝ) := by
          have hn0 : (n : ℝ) ≠ 0 := by
            have : n ≠ 0 := by omega
            exact_mod_cast this
          have hn0' : (n : ℝ) ^ 2 ≠ 0 := by positivity
          field_simp
        rw [h7] at h6
        exact h6
      exact h4
    rw [hFixed] at h1
    exact h1
  have hCopyMain := hMain n (A : BMat n n) ε hε0 hε_le1 hDist'
  have hCopyOAI : (copyCount (fixedH : BMat 66 66) (A : BMat n n) : ℝ) < c * ε ^ C * (n : ℝ) ^ 132 := by
    have h1 : (OAI.Problem348.copyCount (fixedH : BinaryMatrix 66) (A : BinaryMatrix n) : ℝ) < c * ε ^ C * (n : ℝ) ^ 132 := hCopy
    have h2 : (OAI.Problem348.copyCount (fixedH : BinaryMatrix 66) (A : BinaryMatrix n) : ℕ) = copyCount (fixedH : BMat 66 66) (A : BMat n n) := oai_copyCount_eq (H := (fixedH : BMat 66 66)) (A := A)
    have h3 : (copyCount (fixedH : BMat 66 66) (A : BMat n n) : ℝ) = (OAI.Problem348.copyCount (fixedH : BinaryMatrix 66) (A : BinaryMatrix n) : ℝ) := by
      exact_mod_cast h2.symm
    rw [h3]
    exact h1
  have hContra : c * ε ^ C * (n : ℝ) ^ (66 + 66) ≤ (copyCount (fixedH : BMat 66 66) (A : BMat n n) : ℝ) := hCopyMain
  have h132 : (66 + 66 : ℕ) = 132 := rfl
  rw [h132] at hContra
  linarith

theorem infinitely_many_counterexamples :
    ∃ f : ℕ → Pattern, Function.Injective f ∧
      ∀ t, NoZeroLine (f t).2 ∧ ¬ PolyRemoval (f t).2 := by
  obtain ⟨f, hInj, hProp⟩ := exists_injective_counterexample_family (H := (fixedH : BMat 66 66)) oai_noZeroLine oai_not_polyRemoval
  exact ⟨f, hInj, fun t => ⟨(hProp t).2.1, (hProp t).2.2⟩⟩

theorem oai_infinite_family :
    Function.Injective (paddingFamily (fixedH : BMat 66 66)) ∧
      (Set.range (paddingFamily (fixedH : BMat 66 66))).Infinite ∧
        (∀ t : ℕ, NoZeroLine (padding (fixedH : BMat 66 66) t) ∧ ¬ PolyRemoval (padding (fixedH : BMat 66 66) t)) ∧
        (∀ t : ℕ, (paddingFamily (fixedH : BMat 66 66) t).1 = (66 + t, 66 + t)) :=
  infinite_family_of_counterexample (H := (fixedH : BMat 66 66)) oai_noZeroLine oai_not_polyRemoval

#print axioms OAI.Problem348.no_polynomial_removal_bound
#print axioms oai_hamming_eq
#print axioms oai_noZeroLine
#print axioms oai_not_polyRemoval
#print axioms infinitely_many_counterexamples
#print axioms oai_infinite_family
#print axioms oai_fixedMinEdits_eq_editDist
#print axioms oai_copyCount_eq
#print axioms oai_HFree_iff

end OrderedRemoval
