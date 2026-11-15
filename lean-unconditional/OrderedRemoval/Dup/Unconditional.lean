/-
OpenAI's 66 × 66 counterexample has no two equal neighbouring rows or columns, so repeating any
of its rows or columns, any number of times, gives another counterexample.
-/
import OrderedRemoval.Dup.Red
import OrderedRemoval.Unconditional

namespace OrderedRemoval

open OAI.Problem348

theorem oai_reduced : Reduced (fixedH : BMat 66 66) := by
  have hr : ∀ a : Fin 65, ∃ b : Fin 66,
      (fixedH : BMat 66 66) a.castSucc b ≠ (fixedH : BMat 66 66) a.succ b := by
    intro a; fin_cases a <;> decide
  have hc : ∀ b : Fin 65, ∃ a : Fin 66,
      (fixedH : BMat 66 66) a b.castSucc ≠ (fixedH : BMat 66 66) a b.succ := by
    intro b; fin_cases b <;> decide
  constructor
  · intro a a' ha
    obtain ⟨b, hb⟩ := hr ⟨a.val, by have := a'.isLt; omega⟩
    refine ⟨b, ?_⟩
    have e1 : (⟨a.val, by have := a'.isLt; omega⟩ : Fin 65).castSucc = a := by ext; simp
    have e2 : (⟨a.val, by have := a'.isLt; omega⟩ : Fin 65).succ = a' := by ext; simp; omega
    rwa [e1, e2] at hb
  · intro b b' hb'
    obtain ⟨a, ha⟩ := hc ⟨b.val, by have := b'.isLt; omega⟩
    refine ⟨a, ?_⟩
    have e1 : (⟨b.val, by have := b'.isLt; omega⟩ : Fin 65).castSucc = b := by ext; simp
    have e2 : (⟨b.val, by have := b'.isLt; omega⟩ : Fin 65).succ = b' := by ext; simp; omega
    rwa [e1, e2] at ha

/-- Every pattern obtained from OpenAI's `H` by repeating rows and columns is a counterexample. -/
theorem oai_infl_not_polyRemoval {k l : ℕ} {H : BMat k l} (hI : Infl (fixedH : BMat 66 66) H) :
    ¬ PolyRemoval H :=
  not_polyRemoval_of_infl hI oai_reduced (by norm_num) (by norm_num) oai_not_polyRemoval

end OrderedRemoval
