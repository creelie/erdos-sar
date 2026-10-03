import ErdosSar.Rho
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The moment bound (paper Lemma 2.4)

For a finite set `T` of primes let `φ_T(z) = ∏_{p ∈ T, p ∣ z} (1 - 1/p)`. For every `m`,
`#{z ∈ [1, n] : φ_T(z) ≤ x} ≤ n x^m ∏_{p ∈ T} (1 + g_m(p)/p)` with
`g_m(p) = (p/(p-1))^m - 1`. The infinite products are bounded by an exact rational
computation over the primes below `200` (checked by the kernel) and an explicit tail estimate.
-/

namespace ErdosSar

open Finset

/-- `φ_T(z) = ∏_{p ∈ T, p ∣ z} (1 - 1/p)`. -/
noncomputable def phiT (T : Finset ℕ) (z : ℕ) : ℝ := ∏ p ∈ T.filter (· ∣ z), (1 - 1 / (p : ℝ))

/-- `g_m(p) = (p / (p - 1))^m - 1`. -/
noncomputable def gm (m p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 1)) ^ m - 1

theorem card_filter_dvd_Icc (n d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 n).filter (d ∣ ·)).card = n / d := by
  have : (Finset.Icc 1 n).filter (d ∣ ·) = (Finset.Icc 1 (n / d)).image (fun k => d * k) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · rw [Nat.le_div_iff_mul_le hd]; linarith [Nat.mul_comm d k]
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd h1, ?_⟩, Dvd.intro k rfl⟩
      rw [Nat.le_div_iff_mul_le hd] at h2; linarith [Nat.mul_comm d k]
  rw [this, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd h)]
  simp

/-- **Rankin's trick.** For a finite set of primes `T` and `g ≥ 0`,
`∑_{z ≤ n} ∏_{p ∈ T, p ∣ z} (1 + g p) ≤ n ∏_{p ∈ T} (1 + g p / p)`. -/
theorem sum_prod_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (g : ℕ → ℝ) (hg : ∀ p ∈ T, 0 ≤ g p)
    (n : ℕ) :
    ∑ z ∈ Finset.Icc 1 n, ∏ p ∈ T.filter (· ∣ z), (1 + g p) ≤
      n * ∏ p ∈ T, (1 + g p / p) := by
  have key : ∀ z, ∏ p ∈ T.filter (· ∣ z), (1 + g p) =
      ∑ D ∈ T.powerset, if (∏ p ∈ D, p) ∣ z then ∏ p ∈ D, g p else 0 := by
    intro z
    rw [Finset.prod_filter]
    have : ∀ p ∈ T, (if p ∣ z then 1 + g p else 1) = 1 + (if p ∣ z then g p else 0) := by
      intro p _; split_ifs <;> ring
    rw [Finset.prod_congr rfl this, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h
      exact Finset.prod_primes_dvd z
        (fun p hp => (hT p (Finset.mem_powerset.1 hD hp)).prime) h
    · intro h p hp
      exact dvd_trans (Finset.dvd_prod_of_mem _ hp) h
  simp_rw [key]
  rw [Finset.sum_comm]
  have hcount : ∀ D ∈ T.powerset,
      ∑ z ∈ Finset.Icc 1 n, (if (∏ p ∈ D, p) ∣ z then ∏ p ∈ D, g p else 0) ≤
        n * ∏ p ∈ D, (g p / p) := by
    intro D hD
    have hDpos : 0 < ∏ p ∈ D, p :=
      Finset.prod_pos fun p hp => (hT p (Finset.mem_powerset.1 hD hp)).pos
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_dvd_Icc n _ hDpos,
      Finset.prod_div_distrib]
    have hg0 : 0 ≤ ∏ p ∈ D, g p :=
      Finset.prod_nonneg fun p hp => hg p (Finset.mem_powerset.1 hD hp)
    have hc : ((n / ∏ p ∈ D, p : ℕ) : ℝ) ≤ (n : ℝ) / ∏ p ∈ D, (p : ℝ) := by
      rw [← Nat.cast_prod]; exact Nat.cast_div_le
    calc ((n / ∏ p ∈ D, p : ℕ) : ℝ) * ∏ p ∈ D, g p
        ≤ (n : ℝ) / (∏ p ∈ D, (p : ℝ)) * ∏ p ∈ D, g p := by gcongr
      _ = n * ((∏ p ∈ D, g p) / ∏ p ∈ D, (p : ℝ)) := by ring
  calc ∑ D ∈ T.powerset, ∑ z ∈ Finset.Icc 1 n,
        (if (∏ p ∈ D, p) ∣ z then ∏ p ∈ D, g p else 0)
      ≤ ∑ D ∈ T.powerset, n * ∏ p ∈ D, (g p / p) := Finset.sum_le_sum hcount
    _ = n * ∏ p ∈ T, (1 + g p / p) := by rw [← Finset.mul_sum, Finset.prod_one_add]

theorem phiT_pos (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (z : ℕ) : 0 < phiT T z :=
  Finset.prod_pos fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hT p (Finset.mem_filter.1 hp).1).two_le
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith

/-- `(φ_T(z))⁻¹^m = ∏_{p ∈ T, p ∣ z} (1 + g_m p)`. -/
theorem inv_phiT_pow (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (z m : ℕ) :
    ((phiT T z)⁻¹) ^ m = ∏ p ∈ T.filter (· ∣ z), (1 + gm m p) := by
  unfold phiT gm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hT p (Finset.mem_filter.1 hp).1).two_le
  have : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    field_simp
  rw [this]; ring

theorem gm_nonneg (m p : ℕ) (hp : 2 ≤ p) : 0 ≤ gm m p := by
  unfold gm
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have := one_le_pow₀ (n := m) this
  linarith

/-- **Moment bound.** `#{z ∈ [1, n] : φ_T(z) ≤ x} ≤ n x^m ∏_{p ∈ T} (1 + g_m(p)/p)`. -/
theorem card_phiT_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    (((Finset.Icc 1 n).filter (fun z => phiT T z ≤ x)).card : ℝ) ≤
      n * x ^ m * ∏ p ∈ T, (1 + gm m p / p) := by
  set S := (Finset.Icc 1 n).filter (fun z => phiT T z ≤ x)
  have h1 : ∀ z ∈ S, 1 ≤ x ^ m * ((phiT T z)⁻¹) ^ m := by
    intro z hz
    have hz' := (Finset.mem_filter.1 hz).2
    have hpos := phiT_pos T hT z
    rw [← mul_pow]
    apply one_le_pow₀
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]; exact hz'
  have h2 : (S.card : ℝ) ≤ ∑ z ∈ S, x ^ m * ((phiT T z)⁻¹) ^ m := by
    have := Finset.sum_le_sum h1
    simpa using this
  have h3 : ∑ z ∈ S, x ^ m * ((phiT T z)⁻¹) ^ m ≤
      ∑ z ∈ Finset.Icc 1 n, x ^ m * ((phiT T z)⁻¹) ^ m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro z _ _
    have := phiT_pos T hT z
    positivity
  have h4 := sum_prod_le T hT (gm m) (fun p hp => gm_nonneg m p (hT p hp).two_le) n
  have h5 : ∑ z ∈ Finset.Icc 1 n, x ^ m * ((phiT T z)⁻¹) ^ m =
      x ^ m * ∑ z ∈ Finset.Icc 1 n, ∏ p ∈ T.filter (· ∣ z), (1 + gm m p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [inv_phiT_pow T hT]
  have hxm : 0 ≤ x ^ m := pow_nonneg hx.le m
  calc (S.card : ℝ) ≤ _ := h2
    _ ≤ _ := h3
    _ = _ := h5
    _ ≤ x ^ m * (n * ∏ p ∈ T, (1 + gm m p / p)) := mul_le_mul_of_nonneg_left h4 hxm
    _ = n * x ^ m * ∏ p ∈ T, (1 + gm m p / p) := by ring

end ErdosSar
