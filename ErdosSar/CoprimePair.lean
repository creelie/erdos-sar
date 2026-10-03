import ErdosSar.Defs

/-!
# A coprime pair among `o n + 1` odd numbers (Lemma 2.7 of the paper)

If `n ≥ 13` and `O` is a set of at least `o n + 1` odd numbers in `[1, n]`, then `O`
contains two distinct coprime elements. In particular the coprime graph of `O` has an
edge.
-/

namespace ErdosSar

/-- Two distinct odd numbers in the same block `{6k+1, 6k+3, 6k+5}` are coprime. -/
theorem coprime_of_same_block {x y : ℕ} (hx : Odd x) (hy : Odd y) (hne : x ≠ y)
    (hxy : (x - 1) / 6 = (y - 1) / 6) : Nat.Coprime x y := by
  have key : ∀ a b : ℕ, Odd a → Odd b → a < b → (a - 1) / 6 = (b - 1) / 6 →
      Nat.Coprime a b := by
    intro a b ha hb hab h
    obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    have h2 : Nat.Coprime a 2 := Nat.coprime_two_right.2 ha
    have hk : k = 2 ∨ k = 4 := by
      obtain ⟨i, rfl⟩ := ha; obtain ⟨j, hj⟩ := hb; omega
    rcases hk with rfl | rfl
    · rw [add_comm]; exact Nat.coprime_add_self_right.2 h2
    · rw [add_comm]
      exact Nat.coprime_add_self_right.2 (by simpa using Nat.Coprime.pow_right 2 h2)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key x y hx hy h hxy
  · exact (key y x hy hx h hxy.symm).symm

theorem coprime_pair {n : ℕ} (hn : 13 ≤ n) (O : Finset ℕ) (hO : O ⊆ Finset.Icc 1 n)
    (hodd : ∀ x ∈ O, Odd x) (hcard : o n + 1 ≤ O.card) :
    ∃ a ∈ O, ∃ b ∈ O, a ≠ b ∧ Nat.Coprime a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ x ∈ O, x ≤ n := fun x hx => (Finset.mem_Icc.1 (hO hx)).2
  have hge : ∀ x ∈ O, 1 ≤ x := fun x hx => (Finset.mem_Icc.1 (hO hx)).1
  -- the block map is injective on `O`
  have hinj : Set.InjOn (fun x => (x - 1) / 6) (O : Set ℕ) := by
    intro x hx y hy hxy
    by_contra hne
    exact hcon x hx y hy hne (coprime_of_same_block (hodd x hx) (hodd y hy) hne hxy)
  have hmaps : Set.MapsTo (fun x => (x - 1) / 6) (O : Set ℕ)
      (Finset.range ((n - 1) / 6 + 1) : Set ℕ) := by
    intro x hx
    have := hle x hx
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hcardle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcardle
  have ho : o n = (n - 1) / 6 := by unfold o at hcard ⊢; omega
  have hn6 : n % 6 = 1 ∨ n % 6 = 2 := by unfold o at ho; omega
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj (by rw [Finset.card_range]; omega)
  have get : ∀ k, k < (n - 1) / 6 + 1 → ∃ x ∈ O, (x - 1) / 6 = k := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hsurj (by simpa using hk : k ∈ (Finset.range ((n - 1) / 6 + 1) : Set ℕ))
    exact ⟨x, hx, hxk⟩
  obtain ⟨x₀, hx₀, h₀⟩ := get 0 (by omega)
  obtain ⟨x₁, hx₁, h₁⟩ := get 1 (by omega)
  obtain ⟨xK, hxK, hK⟩ := get ((n - 1) / 6) (by omega)
  have o₀ := hodd x₀ hx₀
  have o₁ := hodd x₁ hx₁
  have oK := hodd xK hxK
  have g₀ := hge x₀ hx₀
  have hxK_eq : xK = 6 * ((n - 1) / 6) + 1 := by
    have := hle xK hxK; obtain ⟨j, hj⟩ := oK; omega
  have hx₀' : x₀ = 1 ∨ x₀ = 3 ∨ x₀ = 5 := by obtain ⟨j, hj⟩ := o₀; omega
  have hx₁' : x₁ = 7 ∨ x₁ = 9 ∨ x₁ = 11 := by obtain ⟨j, hj⟩ := o₁; omega
  have h01 := hcon x₀ hx₀ x₁ hx₁ (by omega)
  have h3 : x₀ = 3 := by
    rcases hx₀' with rfl | rfl | rfl <;> rcases hx₁' with rfl | rfl | rfl <;>
      first | rfl | exact absurd (by decide) h01
  subst h3
  have hcop : Nat.Coprime 3 xK := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  exact hcon 3 hx₀ xK hxK (by omega) hcop

end ErdosSar
