import ErdosSar.Counting
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Max

/-!
# The density `ρ'(m)` and the sets `N*(m)`

`ρ'(m) = ∏_{p ∣ m, p ≥ 5} (1 - 1/p)` and `N*(n, m) = {w ∈ E*(n) : gcd(w, m) = 1}`.
-/

namespace ErdosSar

open Finset

/-- The primes `p ≥ 5` dividing `m`. -/
def bigPrimes (m : ℕ) : Finset ℕ := m.primeFactors.filter (5 ≤ ·)

/-- `ρ'(m) = ∏_{p ∣ m, p ≥ 5} (1 - 1/p)`. -/
noncomputable def rho (m : ℕ) : ℝ := ∏ p ∈ bigPrimes m, (1 - 1 / (p : ℝ))

/-- `N*(n, m)`: the elements of `E*(n)` coprime to `m`. -/
def Nstar (n m : ℕ) : Finset ℕ := (Estar n).filter (fun w => Nat.Coprime w m)

theorem mem_bigPrimes {m p : ℕ} : p ∈ bigPrimes m ↔ p.Prime ∧ p ∣ m ∧ m ≠ 0 ∧ 5 ≤ p := by
  simp [bigPrimes, Nat.mem_primeFactors, and_assoc]

theorem bigPrimes_mod_six {m p : ℕ} (hp : p ∈ bigPrimes m) : p % 6 = 1 ∨ p % 6 = 5 := by
  obtain ⟨hpr, -, -, h5⟩ := mem_bigPrimes.1 hp
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).1 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h; omega
  omega

theorem bigPrimes_coprime {m p q : ℕ} (hp : p ∈ bigPrimes m) (hq : q ∈ bigPrimes m)
    (hpq : p ≠ q) : Nat.Coprime p q :=
  (Nat.coprime_primes (mem_bigPrimes.1 hp).1 (mem_bigPrimes.1 hq).1).2 hpq

theorem card_Nstar {n m : ℕ} (hm : Odd m) : (Nstar n m).card = Cnt n (bigPrimes m) := by
  unfold Nstar Estar Cnt
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro w _
  constructor
  · rintro ⟨h6, hc⟩
    refine ⟨h6, fun p hp hpw => ?_⟩
    obtain ⟨hpr, hpm, -, -⟩ := mem_bigPrimes.1 hp
    exact hpr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hpw hpm)
  · rintro ⟨h6, hP⟩
    refine ⟨h6, Nat.coprime_of_dvd fun p hpr hpw hpm => ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
    have h2 : p ≠ 2 := by
      rintro rfl; exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hpm)
    have h3 : p ≠ 3 := by rintro rfl; omega
    have h5 : 5 ≤ p := by
      have := hpr.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
      · exact absurd h h2
      · exact absurd h h3
      · subst h; exact absurd hpr (by decide)
      · exact h
    exact hP p (mem_bigPrimes.2 ⟨hpr, hpm, hm0, h5⟩) hpw

/-- **Paper Lemma 2.3.** For odd `m`, `|#N*(n, m) - (n/3) ρ'(m)| ≤ 2^{ω'(m)} - 1/3`, where
`ω'(m)` is the number of primes `p ≥ 5` dividing `m`. -/
theorem abs_card_Nstar_sub_le {n m : ℕ} (hm : Odd m) :
    |((Nstar n m).card : ℝ) - (n : ℝ) / 3 * rho m| ≤ 2 ^ (bigPrimes m).card - 1 / 3 := by
  rw [card_Nstar hm]
  exact abs_Cnt_sub_mainTerm_le _ (fun p hp => bigPrimes_mod_six hp)
    (fun p hp q hq h => bigPrimes_coprime hp hq h) n

/-! ## Elementary bounds on products over finite sets of integers -/

/-- For a finite set `S` of integers `≥ 2`: `∏_{p ∈ S} (1 - 1/p) ≥ 1/(|S| + 1)`. -/
theorem prod_one_sub_inv_ge (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have ih' := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    -- `s ⊆ [2, a)`, so `a ≥ |s| + 2`
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp =>
      Finset.mem_Ico.2 ⟨hS p (Finset.mem_insert_of_mem hp), ha p hp⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have hca : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast (by omega : s.card + 2 ≤ a)
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    push_cast
    have hpos : (0 : ℝ) < s.card + 1 := by positivity
    have h1 : 1 - 1 / ((s.card : ℝ) + 2) ≤ 1 - 1 / (a : ℝ) := by
      have : 1 / (a : ℝ) ≤ 1 / ((s.card : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) hca
      linarith
    have h0 : 0 ≤ 1 - 1 / ((s.card : ℝ) + 2) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc 1 / ((s.card : ℝ) + 1 + 1)
        = (1 - 1 / ((s.card : ℝ) + 2)) * (1 / ((s.card : ℝ) + 1)) := by
          field_simp; ring
      _ ≤ (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
          apply mul_le_mul h1 ih' (by positivity)
          linarith

/-- For a finite set `S` of integers `≥ 2`: `∏_{p ∈ S} p ≥ (|S| + 1)!`. -/
theorem factorial_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (S.card + 1).factorial ≤ ∏ p ∈ S, p := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have ih' := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp =>
      Finset.mem_Ico.2 ⟨hS p (Finset.mem_insert_of_mem hp), ha p hp⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has, Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih'

theorem rho_nonneg (m : ℕ) : 0 ≤ rho m :=
  Finset.prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by
      exact_mod_cast (show 1 ≤ p by have := (mem_bigPrimes.1 hp).2.2.2; omega)
    rw [sub_nonneg, div_le_one (by linarith)]; exact this

theorem rho_le_one (m : ℕ) : rho m ≤ 1 :=
  Finset.prod_le_one₀
    (fun p hp => by
      have : (1 : ℝ) ≤ p := by
        exact_mod_cast (show 1 ≤ p by have := (mem_bigPrimes.1 hp).2.2.2; omega)
      rw [sub_nonneg, div_le_one (by linarith)]; exact this)
    (fun p hp => by
      have : (0 : ℝ) < p := by
        exact_mod_cast (show 0 < p by have := (mem_bigPrimes.1 hp).2.2.2; omega)
      have : 0 < 1 / (p : ℝ) := by positivity
      linarith)

/-- `ρ'(m) ≥ 1/(ω'(m) + 1)`. -/
theorem rho_ge (m : ℕ) : 1 / (((bigPrimes m).card : ℝ) + 1) ≤ rho m :=
  prod_one_sub_inv_ge _ fun p hp => by have := (mem_bigPrimes.1 hp).2.2.2; omega

/-- `(ω'(m) + 1)! ≤ m` for `m ≥ 1`. -/
theorem factorial_card_bigPrimes_le {m : ℕ} (hm : m ≠ 0) :
    ((bigPrimes m).card + 1).factorial ≤ m := by
  refine (factorial_le_prod _ fun p hp => by have := (mem_bigPrimes.1 hp).2.2.2; omega).trans ?_
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd m)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- Products of factors in `[0, 1]` decrease when the index set grows. -/
theorem prod_le_prod_of_subset_unit {S T : Finset ℕ} (hST : S ⊆ T) (f : ℕ → ℝ)
    (h0 : ∀ p ∈ T, 0 ≤ f p) (h1 : ∀ p ∈ T, f p ≤ 1) :
    ∏ p ∈ T, f p ≤ ∏ p ∈ S, f p := by
  rw [← Finset.prod_sdiff hST]
  have hA : ∏ p ∈ T \ S, f p ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => h0 p (Finset.sdiff_subset hp))
      (fun p hp => h1 p (Finset.sdiff_subset hp))
  have hB : 0 ≤ ∏ p ∈ S, f p := Finset.prod_nonneg fun p hp => h0 p (hST hp)
  nlinarith

theorem bigPrimes_lcm_subset (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    bigPrimes (Nat.lcm a b) ⊆ bigPrimes a ∪ bigPrimes b := by
  intro p hp
  obtain ⟨hpr, hpd, -, h5⟩ := mem_bigPrimes.1 hp
  have : p ∣ a * b := dvd_trans hpd (Nat.lcm_dvd_mul a b)
  rcases (Nat.Prime.dvd_mul hpr).1 this with h | h
  · exact Finset.mem_union_left _ (mem_bigPrimes.2 ⟨hpr, h, ha, h5⟩)
  · exact Finset.mem_union_right _ (mem_bigPrimes.2 ⟨hpr, h, hb, h5⟩)

/-- `ρ'(lcm(a, b)) ≥ ρ'(a) ρ'(b)`. -/
theorem rho_lcm_ge {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : rho a * rho b ≤ rho (Nat.lcm a b) := by
  have hf0 : ∀ p ∈ bigPrimes a ∪ bigPrimes b, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
    have : (1 : ℝ) ≤ p := by
      rcases Finset.mem_union.1 hp with h | h <;>
        exact_mod_cast (show 1 ≤ p by have := (mem_bigPrimes.1 h).2.2.2; omega)
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hf1 : ∀ p ∈ bigPrimes a ∪ bigPrimes b, 1 - 1 / (p : ℝ) ≤ 1 := fun p hp => by
    have : (0 : ℝ) < p := by
      rcases Finset.mem_union.1 hp with h | h <;>
        exact_mod_cast (show 0 < p by have := (mem_bigPrimes.1 h).2.2.2; omega)
    have : 0 < 1 / (p : ℝ) := by positivity
    linarith
  have h1 := prod_le_prod_of_subset_unit (bigPrimes_lcm_subset a b ha hb) _ hf0 hf1
  have h2 := Finset.prod_union_inter (s₁ := bigPrimes a) (s₂ := bigPrimes b)
    (f := fun p : ℕ => 1 - 1 / (p : ℝ))
  have h3 : ∏ p ∈ bigPrimes a ∩ bigPrimes b, (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => hf0 p (Finset.mem_union_left _ (Finset.mem_inter.1 hp).1))
      (fun p hp => hf1 p (Finset.mem_union_left _ (Finset.mem_inter.1 hp).1))
  have h4 : 0 ≤ ∏ p ∈ bigPrimes a ∪ bigPrimes b, (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg hf0
  unfold rho
  nlinarith

end ErdosSar
