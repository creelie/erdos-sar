import Mathlib.Data.Nat.Periodic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Odd multiples of `5` or `7`

Among any `70` consecutive integers exactly `11` are odd and divisible by `5` or `7`; hence at
most `11 (⌊n/70⌋ + 1)` integers in `[1, n]` have this property.
-/

namespace ErdosSar

/-- `z` is odd and divisible by `5` or by `7`. -/
def FiveSeven (z : ℕ) : Prop := z % 2 = 1 ∧ (z % 5 = 0 ∨ z % 7 = 0)

instance : DecidablePred FiveSeven := fun z => by unfold FiveSeven; infer_instance

theorem fiveSeven_periodic : Function.Periodic FiveSeven 70 := by
  intro x
  unfold FiveSeven
  apply propext
  omega

theorem card_fiveSeven_Ico_block (j : ℕ) : ((Finset.Ico j (j + 70)).filter FiveSeven).card = 11 := by
  rw [Nat.filter_Ico_card_eq_of_periodic j 70 FiveSeven fiveSeven_periodic]
  decide

theorem card_fiveSeven_Ico (m : ℕ) :
    ((Finset.Ico 1 (1 + 70 * m)).filter FiveSeven).card = 11 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 1 + 70 * (m + 1) = (1 + 70 * m) + 70 by omega,
      ← Finset.Ico_union_Ico_eq_Ico (a := 1) (b := 1 + 70 * m) (c := 1 + 70 * m + 70)
        (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, card_fiveSeven_Ico_block]
    omega

theorem card_fiveSeven_le (n : ℕ) :
    ((Finset.Icc 1 n).filter FiveSeven).card ≤ 11 * (n / 70 + 1) := by
  calc ((Finset.Icc 1 n).filter FiveSeven).card
      ≤ ((Finset.Ico 1 (1 + 70 * (n / 70 + 1))).filter FiveSeven).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro z hz
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hz ⊢
        omega
    _ = 11 * (n / 70 + 1) := card_fiveSeven_Ico _

end ErdosSar
