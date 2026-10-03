import ErdosSar.Defs

/-! # Relation between the paper's theorem and Question 1 -/

namespace ErdosSar

/-- The paper's main theorem gives Question 1 for every set `A` that omits at most
`n/70` elements of `E* (n)`: every odd `L` with `3 ≤ L ≤ n/3 + 1` has the form `2l+1`
with `1 ≤ l ≤ ⌊n/6⌋ ≤ o n`. -/
theorem question1_of_paperTheorem (h : PaperTheorem) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → T n < A.card →
      70 * (Estar n \ A).card ≤ n →
      ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ n / 3 + 1 → HasCycleOfLength (coprimeGraph A) L := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, fun n hn A hA hT hE L hL h3 hLn => ?_⟩
  obtain ⟨l, rfl⟩ := hL
  exact hn₀ n hn A hA hT hE l (by omega) (by unfold o; omega)

end ErdosSar
