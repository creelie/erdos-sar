import ErdosSar.Setup
import ErdosSar.Assembly
import ErdosSar.Greedy

/-!
# Cycles of length 5 and 7

With the coprime pair `a, b` and easy partners `y` (resp. `y_a, y_b`), the cycles
`a, b, w_b, y, w_a` and `y_a, w_a, a, b, w_b, y_b, w` are built directly.
-/

namespace ErdosSar

open Finset

/-- `ρ'(z) n ≥ 1000` for `z ∈ [1, n]` and `n ≥ N₀`. -/
theorem rho_mul_ge {n z : ℕ} (hn : N₀ ≤ n) (hz : z ∈ Icc 1 n) : 1000 ≤ rho z * n := by
  have hz0 : z ≠ 0 := by have := (Finset.mem_Icc.1 hz).1; omega
  have hzn : z ≤ n ^ 2 := by
    have := (Finset.mem_Icc.1 hz).2
    nlinarith
  have hL := large_n_real hn hz0 hzn
  set K := (bigPrimes z).card
  have h6 : 1 / ((K : ℝ) + 1) ≤ rho z := rho_ge z
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hrz : 1 ≤ rho z * (K + 1) := by rw [div_le_iff₀ hK1] at h6; linarith
  have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem cycle_five {n : ℕ} (hn : N₀ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n) {a b y : ℕ}
    (haA : a ∈ A) (hbA : b ∈ A) (hyA : y ∈ A) (ha2 : a % 2 = 1) (hb2 : b % 2 = 1)
    (hy2 : y % 2 = 1) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hcop : Nat.Coprime a b)
    (haU : Undamaged n A a) (hbU : Undamaged n A b) (hyE : 3 / 4 ≤ rho y) :
    HasCycleOfLength (coprimeGraph A) 5 := by
  classical
  obtain ⟨w, hw, hwinj⟩ := greedy_choice ({0, 1} : Finset ℕ) (fun _ => (0 : ℕ))
    (fun i => if i = 0 then NA n A (Nat.lcm y a) else NA n A (Nat.lcm y b)) (by
      intro i hi
      rw [Finset.filter_true_of_mem (fun _ _ => le_refl _),
        Finset.card_pair_eq_two_iff.2 (by norm_num)]
      have hz : ∀ z, z ∈ A → z % 2 = 1 → Undamaged n A z →
          2 ≤ (NA n A (Nat.lcm y z)).card := by
        intro z hzA hz2 hzU
        have := NA_card_master (A := A) hn (hA hyA) (hA hzA) hy2 hz2 hyE hzU
        have : 0 ≤ rho z * n / 280 := by have := rho_nonneg z; positivity
        have : (2 : ℝ) ≤ (NA n A (Nat.lcm y z)).card := by linarith
        exact_mod_cast this
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa using hz a haA ha2 haU
      · simpa using hz b hbA hb2 hbU)
  have h0 : w 0 ∈ NA n A (Nat.lcm y a) := by simpa using hw 0 (by simp)
  have h1 : w 1 ∈ NA n A (Nat.lcm y b) := by simpa using hw 1 (by simp)
  have hne : w 0 ≠ w 1 := fun h => by
    have := hwinj (by simp) (by simp) h; simp at this
  obtain ⟨h0N, h0A⟩ := mem_NA.1 h0
  obtain ⟨h1N, h1A⟩ := mem_NA.1 h1
  have e0 := even_of_mem_Estar (mem_Nstar.1 h0N).1
  have e1 := even_of_mem_Estar (mem_Nstar.1 h1N).1
  have c0 := coprime_of_mem_Nstar_lcm h0N
  have c1 := coprime_of_mem_Nstar_lcm h1N
  have := hasCycle_of_list A a [b, w 1, y, w 0]
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        not_or, not_false_eq_true, and_true]
      omega)
    (by simp)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by
      simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
        List.IsChain.singleton, and_true]
      exact ⟨hcop, c1.2.symm, c1.1, c0.1.symm, c0.2⟩)
  simpa using this

theorem cycle_seven {n : ℕ} (hn : N₀ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    {a b ya yb : ℕ} (haA : a ∈ A) (hbA : b ∈ A) (hyaA : ya ∈ A) (hybA : yb ∈ A)
    (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) (hya2 : ya % 2 = 1) (hyb2 : yb % 2 = 1)
    (hab : a ≠ b) (h1 : ya ≠ a) (h2 : ya ≠ b) (h3 : yb ≠ a) (h4 : yb ≠ b) (h5 : ya ≠ yb)
    (hcop : Nat.Coprime a b) (haU : Undamaged n A a) (hbU : Undamaged n A b)
    (hybU : Undamaged n A yb) (hyaE : 3 / 4 ≤ rho ya) (hybE : 3 / 4 ≤ rho yb) :
    HasCycleOfLength (coprimeGraph A) 7 := by
  classical
  have hz : ∀ y z, y ∈ A → z ∈ A → y % 2 = 1 → z % 2 = 1 → 3 / 4 ≤ rho y →
      Undamaged n A z → 3 ≤ (NA n A (Nat.lcm y z)).card := by
    intro y z hyA hzA hy2 hz2 hyE hzU
    have := NA_card_master (A := A) hn (hA hyA) (hA hzA) hy2 hz2 hyE hzU
    have := rho_mul_ge hn (hA hzA)
    have : (3 : ℝ) ≤ (NA n A (Nat.lcm y z)).card := by linarith
    exact_mod_cast this
  obtain ⟨w, hw, hwinj⟩ := greedy_choice ({0, 1, 2} : Finset ℕ) (fun _ => (0 : ℕ))
    (fun i => if i = 0 then NA n A (Nat.lcm ya a) else if i = 1 then NA n A (Nat.lcm yb b)
      else NA n A (Nat.lcm ya yb)) (by
      intro i hi
      rw [Finset.filter_true_of_mem (fun _ _ => le_refl _)]
      have hc : ({0, 1, 2} : Finset ℕ).card = 3 := by decide
      rw [hc]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simpa using hz ya a hyaA haA hya2 ha2 hyaE haU
      · simpa using hz yb b hybA hbA hyb2 hb2 hybE hbU
      · simpa using hz ya yb hyaA hybA hya2 hyb2 hyaE hybU)
  have g0 : w 0 ∈ NA n A (Nat.lcm ya a) := by simpa using hw 0 (by simp)
  have g1 : w 1 ∈ NA n A (Nat.lcm yb b) := by simpa using hw 1 (by simp)
  have g2 : w 2 ∈ NA n A (Nat.lcm ya yb) := by simpa using hw 2 (by simp)
  have n01 : w 0 ≠ w 1 := fun h => by have := hwinj (by simp) (by simp) h; simp at this
  have n02 : w 0 ≠ w 2 := fun h => by have := hwinj (by simp) (by simp) h; simp at this
  have n12 : w 1 ≠ w 2 := fun h => by have := hwinj (by simp) (by simp) h; simp at this
  obtain ⟨g0N, g0A⟩ := mem_NA.1 g0
  obtain ⟨g1N, g1A⟩ := mem_NA.1 g1
  obtain ⟨g2N, g2A⟩ := mem_NA.1 g2
  have e0 := even_of_mem_Estar (mem_Nstar.1 g0N).1
  have e1 := even_of_mem_Estar (mem_Nstar.1 g1N).1
  have e2 := even_of_mem_Estar (mem_Nstar.1 g2N).1
  have c0 := coprime_of_mem_Nstar_lcm g0N
  have c1 := coprime_of_mem_Nstar_lcm g1N
  have c2 := coprime_of_mem_Nstar_lcm g2N
  have := hasCycle_of_list A ya [w 0, a, b, w 1, yb, w 2]
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        not_or, not_false_eq_true, and_true]
      omega)
    (by simp)
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by
      simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
        List.IsChain.singleton, and_true]
      exact ⟨c0.1.symm, c0.2, hcop, c1.2.symm, c1.1, c2.2.symm, c2.1⟩)
  simpa using this

end ErdosSar
