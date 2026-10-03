import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact rational certificates for the moment constants

`F s m = ∏_{s ≤ p < 200, p prime} (1 + ((p/(p-1))^m - 1)/p)` computed in `ℚ`. The two
inequalities below are checked by the kernel; together with the tail estimate of
`ErdosSar.Moment` they give the constants of paper Lemma 2.4.
-/

namespace ErdosSar

/-- The finite part of the Euler product over primes `s ≤ p < 200`. -/
def Fq (s m : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range 200).filter (fun p => s ≤ p ∧ p.Prime),
    (1 + (((p : ℚ) / (p - 1)) ^ m - 1) / p)

set_option maxRecDepth 100000 in
/-- Hard numbers: `(14/25)^37 · F(5, 37) ≤ (1/1000)(1 - 74/199)`. -/
theorem Fq_five : (14 / 25 : ℚ) ^ 37 * Fq 5 37 ≤ 1 / 1000 * (1 - 74 / 199) := by
  unfold Fq
  decide +kernel

set_option maxRecDepth 100000 in
/-- Easy numbers: `(3/4)^54 · F(11, 54) ≤ (1/1000)(1 - 108/199)`. -/
theorem Fq_eleven : (3 / 4 : ℚ) ^ 54 * Fq 11 54 ≤ 1 / 1000 * (1 - 108 / 199) := by
  unfold Fq
  decide +kernel

end ErdosSar
