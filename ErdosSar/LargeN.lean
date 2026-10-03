import ErdosSar.Rho

/-!
# Uniform control of `2^{ω'(m)}` for `m ≤ n²`

Since `(ω'(m) + 1)! ≤ m`, the number `K = ω'(m)` is tiny compared with `n` when `m ≤ n²`.
We record the single explicit consequence used in the proof: for `n ≥ N₀` and `1 ≤ m ≤ n²`,
`1000 (K + 1) 2^K ≤ n`.
-/

namespace ErdosSar

theorem sq_le_factorial_aux : ∀ K, 22 ≤ K →
    (1000 * (K + 1) * 2 ^ K) ^ 2 ≤ (K + 1).factorial := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => decide
  | succ K hK ih =>
    rw [Nat.factorial_succ]
    have e : (1000 * (K + 1 + 1) * 2 ^ (K + 1)) ^ 2 * (K + 1) ^ 2 =
        4 * (K + 2) ^ 2 * (1000 * (K + 1) * 2 ^ K) ^ 2 := by ring
    have h1 : (1000 * (K + 1 + 1) * 2 ^ (K + 1)) ^ 2 * (K + 1) ^ 2 ≤
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

/-- The explicit threshold. -/
def N₀ : ℕ := 1000 * 23 * 2 ^ 22

theorem large_n {n m : ℕ} (hn : N₀ ≤ n) (hm : m ≠ 0) (hmn : m ≤ n ^ 2) :
    1000 * ((bigPrimes m).card + 1) * 2 ^ (bigPrimes m).card ≤ n := by
  set K := (bigPrimes m).card
  rcases le_or_gt 22 K with hK | hK
  · have h1 := sq_le_factorial_aux K hK
    have h2 := factorial_card_bigPrimes_le hm
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (h1.trans (h2.trans hmn))
  · refine le_trans ?_ hn
    unfold N₀
    have : 2 ^ K ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hK.le
    have : K + 1 ≤ 23 := by omega
    calc 1000 * (K + 1) * 2 ^ K ≤ 1000 * 23 * 2 ^ 22 := by gcongr

end ErdosSar
