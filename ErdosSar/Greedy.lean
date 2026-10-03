import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-!
# Greedy choice of distinct representatives

If every index `i ∈ I` has at least as many candidates as there are indices whose key is at
most the key of `i`, then distinct candidates can be chosen for all indices: treat the indices
in increasing order of their keys.
-/

namespace ErdosSar

open Finset

theorem greedy_choice {ι κ : Type*} [DecidableEq ι] [LinearOrder κ] (I : Finset ι) (key : ι → κ)
    (C : ι → Finset ℕ) (h : ∀ i ∈ I, (I.filter (fun j => key j ≤ key i)).card ≤ (C i).card) :
    ∃ w : ι → ℕ, (∀ i ∈ I, w i ∈ C i) ∧ Set.InjOn w I := by
  induction I using Finset.induction_on_max_value key with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a s ha hmax ih =>
    have hs : ∀ i ∈ s, (s.filter (fun j => key j ≤ key i)).card ≤ (C i).card := by
      intro i hi
      refine le_trans (Finset.card_le_card ?_) (h i (Finset.mem_insert_of_mem hi))
      exact Finset.filter_subset_filter _ (Finset.subset_insert a s)
    obtain ⟨w, hwC, hwinj⟩ := ih hs
    have hall : (insert a s).filter (fun j => key j ≤ key a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact le_refl _
      · exact hmax j hj
    have hCa := h a (Finset.mem_insert_self a s)
    rw [hall, Finset.card_insert_of_notMem ha] at hCa
    have himg : (s.image w).card < (C a).card :=
      lt_of_lt_of_le (Nat.lt_succ_of_le Finset.card_image_le) hCa
    obtain ⟨c, hcC, hcw⟩ : ∃ c ∈ C a, c ∉ s.image w := by
      by_contra hcon
      push Not at hcon
      exact absurd (Finset.card_le_card hcon) (not_le.2 himg)
    refine ⟨Function.update w a c, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simp [hcC]
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        simp [hia, hwC i hi]
    · intro i hi j hj hij
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · rfl
      · have hja : j ≠ i := fun h => ha (h ▸ hj)
        simp [hja] at hij
        exact absurd (Finset.mem_image.2 ⟨j, hj, hij.symm⟩) hcw
      · have hia : i ≠ j := fun h => ha (h ▸ hi)
        simp [hia] at hij
        exact absurd (Finset.mem_image.2 ⟨i, hi, hij⟩) hcw
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        have hja : j ≠ a := fun h => ha (h ▸ hj)
        simp [hia, hja] at hij
        exact hwinj hi hj hij

end ErdosSar
