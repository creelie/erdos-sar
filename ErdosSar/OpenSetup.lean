import ErdosSar.Assembly
import ErdosSar.Greedy
import ErdosSar.CoprimePair
import ErdosSar.Setup
import ErdosSar.CountingR

/-!
# Set-up for the open case

The sets of odd elements and of units of `A` whose density `ρ'` is at least a threshold, the
multiples of `6`, a sharper form of the uniform bound on `2^{ω'(m)}`, and the counting estimates
in that form.
-/

namespace ErdosSar

open Finset

/-- The odd elements `z ∈ A` with `ρ'(z) ≥ t`. -/
noncomputable def Good (A : Finset ℕ) (t : ℝ) : Finset ℕ :=
  A.filter (fun z => z % 2 = 1 ∧ t ≤ rho z)

/-- The elements `z ∈ A` with `z ≡ ±1 (mod 6)` and `ρ'(z) ≥ t`. -/
noncomputable def GoodU (A : Finset ℕ) (t : ℝ) : Finset ℕ :=
  A.filter (fun z => (z % 6 = 1 ∨ z % 6 = 5) ∧ t ≤ rho z)

/-- The multiples of `6` in `[1, n]`. -/
def M6 (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun z => z % 6 = 0)

theorem mem_Good {A : Finset ℕ} {t : ℝ} {z : ℕ} :
    z ∈ Good A t ↔ z ∈ A ∧ z % 2 = 1 ∧ t ≤ rho z := by
  simp [Good]

theorem mem_GoodU {A : Finset ℕ} {t : ℝ} {z : ℕ} :
    z ∈ GoodU A t ↔ z ∈ A ∧ (z % 6 = 1 ∨ z % 6 = 5) ∧ t ≤ rho z := by
  simp [GoodU]

theorem mem_M6 {n z : ℕ} : z ∈ M6 n ↔ (1 ≤ z ∧ z ≤ n) ∧ z % 6 = 0 := by
  simp [M6]

/-! ## The uniform bound with constant `10⁶` -/

theorem sq_le_factorial_big : ∀ K, 29 ≤ K →
    (10 ^ 6 * (K + 1) * 2 ^ K) ^ 2 ≤ (K + 1).factorial := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => decide
  | succ K hK ih =>
    rw [Nat.factorial_succ]
    have e : (10 ^ 6 * (K + 1 + 1) * 2 ^ (K + 1)) ^ 2 * (K + 1) ^ 2 =
        4 * (K + 2) ^ 2 * (10 ^ 6 * (K + 1) * 2 ^ K) ^ 2 := by ring
    have h1 : (10 ^ 6 * (K + 1 + 1) * 2 ^ (K + 1)) ^ 2 * (K + 1) ^ 2 ≤
        4 * (K + 2) ^ 2 * (K + 1).factorial := by
      rw [e]; exact Nat.mul_le_mul_left _ ih
    have h2 : 4 * (K + 2) ^ 2 * (K + 1).factorial ≤
        (K + 1 + 1) * (K + 1).factorial * (K + 1) ^ 2 := by
      have : 4 * (K + 2) ≤ (K + 1) ^ 2 := by nlinarith
      calc 4 * (K + 2) ^ 2 * (K + 1).factorial
          = (4 * (K + 2)) * ((K + 2) * (K + 1).factorial) := by ring
        _ ≤ (K + 1) ^ 2 * ((K + 2) * (K + 1).factorial) := Nat.mul_le_mul_right _ this
        _ = (K + 1 + 1) * (K + 1).factorial * (K + 1) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right (h1.trans h2) (by positivity)

/-- The threshold for the open case. -/
def N₁ : ℕ := 10 ^ 6 * 30 * 2 ^ 29

theorem N₀_le_N₁ : N₀ ≤ N₁ := by unfold N₀ N₁; norm_num

theorem large_n_big {n m : ℕ} (hn : N₁ ≤ n) (hm : m ≠ 0) (hmn : m ≤ n ^ 2) :
    10 ^ 6 * ((bigPrimes m).card + 1) * 2 ^ (bigPrimes m).card ≤ n := by
  set K := (bigPrimes m).card
  rcases le_or_gt 29 K with hK | hK
  · have h1 := sq_le_factorial_big K hK
    have h2 := factorial_card_bigPrimes_le hm
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (h1.trans (h2.trans hmn))
  · refine le_trans ?_ hn
    unfold N₁
    have : 2 ^ K ≤ 2 ^ 29 := Nat.pow_le_pow_right (by norm_num) hK.le
    have : K + 1 ≤ 30 := by omega
    calc 10 ^ 6 * (K + 1) * 2 ^ K ≤ 10 ^ 6 * 30 * 2 ^ 29 := by gcongr

theorem two_pow_le_big {n m : ℕ} (hn : N₁ ≤ n) (hm : m ≠ 0) (hmn : m ≤ n ^ 2) :
    (2 : ℝ) ^ (bigPrimes m).card ≤ n / 10 ^ 6 := by
  have h := large_n_big hn hm hmn
  have h' : (10 : ℝ) ^ 6 * ((bigPrimes m).card + 1) * 2 ^ (bigPrimes m).card ≤ n := by
    exact_mod_cast h
  have hK : (1 : ℝ) ≤ (bigPrimes m).card + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (bigPrimes m).card; linarith
  have h2 : (0 : ℝ) < 2 ^ (bigPrimes m).card := by positivity
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

theorem n_ge_of_N₁ {n : ℕ} (hn : N₁ ≤ n) : (10 ^ 15 : ℝ) ≤ n := by
  have : (10 ^ 15 : ℕ) ≤ n := le_trans (by unfold N₁; norm_num) hn
  exact_mod_cast this

/-! ## Counting estimates -/

theorem card_Nstar_ge_big {n m : ℕ} (hn : N₁ ≤ n) (hm : Odd m) (hmn : m ≤ n ^ 2) :
    (n : ℝ) / 3 * rho m - n / 10 ^ 6 ≤ (Nstar n m).card := by
  have h1 := card_Nstar_ge (n := n) hm
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have h2 := two_pow_le_big hn hm0 hmn
  linarith

theorem card_class_coprime_ge_big {n m : ℕ} {R : Finset ℕ} (hR : SymRes R) (hn : N₁ ≤ n)
    (hm0 : m ≠ 0) (hmn : m ≤ n ^ 2) (h2 : 2 ∣ m → ∀ r ∈ R, r % 2 = 1)
    (h3 : 3 ∣ m → ∀ r ∈ R, r % 3 ≠ 0) :
    (n : ℝ) / 6 * R.card * rho m - R.card * (n / 10 ^ 6) ≤
      (((Icc 1 n).filter (fun w => w % 6 ∈ R ∧ Nat.Coprime w m)).card : ℝ) := by
  have h1 := abs_card_class_coprime_sub_le (n := n) hR hm0 h2 h3
  have h4 := two_pow_le_big hn hm0 hmn
  have h5 := neg_abs_le ((((Icc 1 n).filter (fun w => w % 6 ∈ R ∧ Nat.Coprime w m)).card : ℝ) -
    (n : ℝ) / 6 * R.card * rho m)
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have : (R.card : ℝ) * (2 ^ (bigPrimes m).card - 1 / 6) ≤ R.card * (n / 10 ^ 6) :=
    mul_le_mul_of_nonneg_left (by linarith) hR0
  linarith

theorem lcm_unit {a b : ℕ} (ha : a % 6 = 1 ∨ a % 6 = 5) (hb : b % 6 = 1 ∨ b % 6 = 5) :
    ¬ 2 ∣ Nat.lcm a b ∧ ¬ 3 ∣ Nat.lcm a b := by
  have hab : ¬ 2 ∣ a * b ∧ ¬ 3 ∣ a * b := by
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h <;> omega
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h <;> omega
  exact ⟨fun h => hab.1 (dvd_trans h (Nat.lcm_dvd_mul a b)),
    fun h => hab.2 (dvd_trans h (Nat.lcm_dvd_mul a b))⟩

theorem rho_lcm_ge_of {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {x y : ℝ} (hx : 0 ≤ x)
    (hxa : x ≤ rho a) (hyb : y ≤ rho b) : x * y ≤ rho (Nat.lcm a b) := by
  have := rho_lcm_ge ha hb
  have h0 := rho_nonneg b
  calc x * y ≤ x * rho b := mul_le_mul_of_nonneg_left hyb hx
    _ ≤ rho a * rho b := mul_le_mul_of_nonneg_right hxa h0
    _ ≤ _ := this

end ErdosSar
