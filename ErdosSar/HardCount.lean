import ErdosSar.Moment
import ErdosSar.Numerics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# How many numbers are hard (paper Corollary 2.5)

The Euler products of the moment bound are split into the primes below `200`, handled by the
kernel-checked certificates `Fq_five` and `Fq_eleven`, and the primes `p ≥ 200`, where
`g_m(p) ≤ 2m/p` and `∑_{p ≥ 200} 1/p² ≤ 1/199`.
-/

namespace ErdosSar

open Finset

/-- The primes in `[s, n]`. -/
def primesIn (s n : ℕ) : Finset ℕ := (Finset.Icc s n).filter Nat.Prime

theorem mem_primesIn {s n p : ℕ} : p ∈ primesIn s n ↔ (s ≤ p ∧ p ≤ n) ∧ p.Prime := by
  simp [primesIn]

/-- `(1 + u)^m (1 - m u) ≤ 1` for `0 ≤ u ≤ 1`. -/
theorem one_add_pow_mul_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (m : ℕ) :
    (1 + u) ^ m * (1 - m * u) ≤ 1 := by
  have h1 : 1 - m * u ≤ (1 - u) ^ m := by
    have := one_add_mul_le_pow (a := -u) (by linarith) m
    have e : (1 : ℝ) + -u = 1 - u := by ring
    rw [e] at this; linarith
  have h2 : (1 + u) ^ m * (1 - u) ^ m ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  calc (1 + u) ^ m * (1 - m * u) ≤ (1 + u) ^ m * (1 - u) ^ m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 := h2

/-- `g_m(p) ≤ 2m/p` for `p ≥ 2m + 2`. -/
theorem gm_le (m p : ℕ) (hp : 2 * m + 2 ≤ p) : gm m p ≤ 2 * m / p := by
  unfold gm
  have hq : (2 * m + 2 : ℝ) ≤ p := by exact_mod_cast hp
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set u : ℝ := 1 / ((p : ℝ) - 1) with hu
  have hdiv : (p : ℝ) / ((p : ℝ) - 1) = 1 + u := by rw [hu]; field_simp; ring
  rw [hdiv]
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hp1]; linarith
  have key := one_add_pow_mul_le u hu0 hu1 m
  set X := (1 + u) ^ m with hX
  have hX1 : 1 ≤ X := one_le_pow₀ (by linarith)
  -- `X (p - 1 - m) ≤ p - 1`
  have hmu : (m : ℝ) * u * ((p : ℝ) - 1) = m := by rw [hu]; field_simp
  have h3 : X * ((p : ℝ) - 1 - m) ≤ (p : ℝ) - 1 := by
    have := mul_le_mul_of_nonneg_right key hp1.le
    nlinarith
  rw [le_div_iff₀ hp0]
  nlinarith [mul_nonneg (sub_nonneg.2 hX1) (show (0 : ℝ) ≤ (p : ℝ) - 2 - 2 * m by linarith)]

/-- `(∏ (1 + a_p)) (1 - ∑ a_p) ≤ 1` for `a_p ≥ 0`. -/
theorem prod_one_add_mul_le (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ S, 0 ≤ a p) :
    (∏ p ∈ S, (1 + a p)) * (1 - ∑ p ∈ S, a p) ≤ 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    have ih' := ih (fun p hp => ha p (Finset.mem_insert_of_mem hp))
    have haq := ha q (Finset.mem_insert_self q s)
    have hs : 0 ≤ ∑ p ∈ s, a p :=
      Finset.sum_nonneg fun p hp => ha p (Finset.mem_insert_of_mem hp)
    have hP : 0 ≤ ∏ p ∈ s, (1 + a p) :=
      Finset.prod_nonneg fun p hp => by linarith [ha p (Finset.mem_insert_of_mem hp)]
    nlinarith [mul_nonneg hP (mul_nonneg haq hs), mul_nonneg hP (mul_nonneg haq haq)]

theorem sum_Ico_telescope (k : ℕ) :
    ∑ p ∈ Finset.Ico 200 (200 + k), (1 / ((p : ℝ) - 1) - 1 / p) = 1 / 199 - 1 / (199 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 200 + (k + 1) = (200 + k) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    rw [show (199 : ℝ) + ((k : ℝ) + 1) = 200 + k by ring, show (200 : ℝ) + k - 1 = 199 + k by ring]
    ring

/-- `∑_{p ∈ T} 1/p² ≤ 1/199` for a finite set `T` of integers `≥ 200`. -/
theorem sum_inv_sq_le (T : Finset ℕ) (hT : ∀ p ∈ T, 200 ≤ p) :
    ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ 1 / 199 := by
  set k := T.sup id + 1
  have hsub : T ⊆ Finset.Ico 200 (200 + k) := fun p hp =>
    Finset.mem_Ico.2 ⟨hT p hp, by
      have : p ≤ T.sup id := Finset.le_sup (f := id) hp
      omega⟩
  have hterm : ∀ p ∈ Finset.Ico 200 (200 + k), 1 / ((p : ℝ) ^ 2) ≤ 1 / ((p : ℝ) - 1) - 1 / p := by
    intro p hp
    have h200 : (200 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Ico.1 hp).1
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (0 : ℝ) < p - 1 := by linarith
      exact this.ne'
    have hp0 : (p : ℝ) ≠ 0 := by
      have : (0 : ℝ) < p := by linarith
      exact this.ne'
    have e : 1 / ((p : ℝ) - 1) - 1 / p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [div_sub_div _ _ hp1 hp0]; congr 1 <;> ring
    rw [e]
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hnn : ∀ p ∈ Finset.Ico 200 (200 + k), p ∉ T → 0 ≤ 1 / ((p : ℝ) - 1) - 1 / p := by
    intro p hp _
    have := hterm p hp
    have : 0 ≤ 1 / ((p : ℝ) ^ 2) := by positivity
    linarith
  calc ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ ∑ p ∈ T, (1 / ((p : ℝ) - 1) - 1 / p) :=
        Finset.sum_le_sum fun p hp => hterm p (hsub hp)
    _ ≤ ∑ p ∈ Finset.Ico 200 (200 + k), (1 / ((p : ℝ) - 1) - 1 / p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = 1 / 199 - 1 / (199 + k) := sum_Ico_telescope k
    _ ≤ 1 / 199 := by
        have : 0 ≤ 1 / ((199 : ℝ) + k) := by positivity
        linarith

theorem one_le_one_add_gm_div (m p : ℕ) (hp : 2 ≤ p) : 1 ≤ 1 + gm m p / p := by
  have := gm_nonneg m p hp
  have : 0 ≤ gm m p / p := by positivity
  linarith

/-- The tail of the Euler product: primes `p ≥ 200`. -/
theorem prod_tail_le (T : Finset ℕ) (hT : ∀ p ∈ T, 200 ≤ p) (m : ℕ) (hm : 2 * m + 2 ≤ 200) :
    (∏ p ∈ T, (1 + gm m p / p)) * (1 - 2 * m / 199) ≤ 1 := by
  have ha : ∀ p ∈ T, 0 ≤ gm m p / p := fun p hp => by
    have := gm_nonneg m p (by have := hT p hp; omega); positivity
  have hsum : ∑ p ∈ T, gm m p / p ≤ 2 * m / 199 := by
    calc ∑ p ∈ T, gm m p / p ≤ ∑ p ∈ T, (2 * m) * (1 / ((p : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp200 : (200 : ℝ) ≤ p := by exact_mod_cast hT p hp
          have hg := gm_le m p (by have := hT p hp; omega)
          rw [div_le_iff₀ (by linarith)]
          calc gm m p ≤ 2 * m / p := hg
            _ = 2 * m * (1 / (p : ℝ) ^ 2) * p := by field_simp
      _ = (2 * m) * ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ (2 * m) * (1 / 199) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sq_le T hT); positivity
      _ = 2 * m / 199 := by ring
  have h := prod_one_add_mul_le T (fun p => gm m p / p) ha
  have hP : 1 ≤ ∏ p ∈ T, (1 + gm m p / p) :=
    Finset.one_le_prod₀ fun p hp => one_le_one_add_gm_div m p (by have := hT p hp; omega)
  nlinarith

/-- The finite Euler product as a real number. -/
theorem Fq_cast (s m : ℕ) :
    ((Fq s m : ℚ) : ℝ) = ∏ p ∈ (Finset.range 200).filter (fun p => s ≤ p ∧ p.Prime),
      (1 + gm m p / p) := by
  unfold Fq gm
  push_cast [Rat.cast_pow]
  rfl

/-- `∏_{p ∈ [s, n] prime} (1 + g_m(p)/p) · (1 - 2m/199) ≤ F(s, m)`. -/
theorem prod_primesIn_le (s m n : ℕ) (hm : 2 * m + 2 ≤ 200) :
    (∏ p ∈ primesIn s n, (1 + gm m p / p)) * (1 - 2 * m / 199) ≤ ((Fq s m : ℚ) : ℝ) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (primesIn s n) (· < 200)]
  have hlow : ∏ p ∈ (primesIn s n).filter (· < 200), (1 + gm m p / p) ≤ ((Fq s m : ℚ) : ℝ) := by
    rw [Fq_cast]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨⟨h1, -⟩, hpr⟩ := mem_primesIn.1 hp1
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hp2, h1, hpr⟩
    · intro p hp
      obtain ⟨hp1, -⟩ := Finset.mem_filter.1 hp
      have := one_le_one_add_gm_div m p (mem_primesIn.1 hp1).2.two_le
      linarith
    · intro p hp _
      exact one_le_one_add_gm_div m p (Finset.mem_filter.1 hp).2.2.two_le
  have htail := prod_tail_le ((primesIn s n).filter (fun p => ¬ p < 200))
    (fun p hp => by have := (Finset.mem_filter.1 hp).2; omega) m hm
  have hL0 : 0 ≤ ∏ p ∈ (primesIn s n).filter (· < 200), (1 + gm m p / p) :=
    Finset.prod_nonneg fun p hp => by
      have := one_le_one_add_gm_div m p (mem_primesIn.1 (Finset.mem_filter.1 hp).1).2.two_le
      linarith
  calc (∏ p ∈ (primesIn s n).filter (· < 200), (1 + gm m p / p)) *
        (∏ p ∈ (primesIn s n).filter (fun p => ¬ p < 200), (1 + gm m p / p)) *
          (1 - 2 * m / 199)
      = (∏ p ∈ (primesIn s n).filter (· < 200), (1 + gm m p / p)) *
        ((∏ p ∈ (primesIn s n).filter (fun p => ¬ p < 200), (1 + gm m p / p)) *
          (1 - 2 * m / 199)) := by ring
    _ ≤ (∏ p ∈ (primesIn s n).filter (· < 200), (1 + gm m p / p)) * 1 :=
        mul_le_mul_of_nonneg_left htail hL0
    _ ≤ ((Fq s m : ℚ) : ℝ) := by rw [mul_one]; exact hlow

/-- For `1 ≤ z ≤ n`, `φ_T(z) = ρ'(z)` with `T` the primes in `[5, n]`. -/
theorem phiT_primesIn_five {n z : ℕ} (hz1 : 1 ≤ z) (hzn : z ≤ n) :
    phiT (primesIn 5 n) z = rho z := by
  unfold phiT rho
  congr 1
  ext p
  rw [Finset.mem_filter, mem_primesIn, mem_bigPrimes]
  constructor
  · rintro ⟨⟨⟨h5, -⟩, hpr⟩, hpz⟩
    exact ⟨hpr, hpz, by omega, h5⟩
  · rintro ⟨hpr, hpz, -, h5⟩
    exact ⟨⟨⟨h5, (Nat.le_of_dvd (by omega) hpz).trans hzn⟩, hpr⟩, hpz⟩

/-- **Paper Corollary 2.5(a).** For `0 < x ≤ 14/25`, `#{z ≤ n : ρ'(z) ≤ x} ≤ x n / 560`. -/
theorem card_rho_le (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 14 / 25) :
    (((Finset.Icc 1 n).filter (fun z => rho z ≤ x)).card : ℝ) ≤ x * n / 560 := by
  have hset : (Finset.Icc 1 n).filter (fun z => rho z ≤ x) =
      (Finset.Icc 1 n).filter (fun z => phiT (primesIn 5 n) z ≤ x) := by
    apply Finset.filter_congr
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hz
    rw [phiT_primesIn_five h1 h2]
  rw [hset]
  have hT : ∀ p ∈ primesIn 5 n, p.Prime := fun p hp => (mem_primesIn.1 hp).2
  have h1 := card_phiT_le (primesIn 5 n) hT n 37 hx0
  have h2 := prod_primesIn_le 5 37 n (by norm_num)
  have h3 : ((14 / 25 : ℚ) : ℝ) ^ 37 * ((Fq 5 37 : ℚ) : ℝ) ≤
      ((1 / 1000 * (1 - 74 / 199) : ℚ) : ℝ) := by
    rw [← Rat.cast_pow, ← Rat.cast_mul]; exact_mod_cast Fq_five
  push_cast at h2 h3
  set y := x / (14 / 25) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by norm_num)]; exact hx
  have hxy : x = 14 / 25 * y := by rw [hy]; field_simp
  have hpow : y ^ 37 ≤ y := pow_le_of_le_one hy0 hy1 (by norm_num)
  have hP0 : 0 ≤ ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p) :=
    Finset.prod_nonneg fun p hp => by
      have := one_le_one_add_gm_div 37 p (hT p hp).two_le; linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- `x^37 P ≤ (14/25)^37 y F / (1 - 74/199) ≤ y / 1000`
  have h4 : x ^ 37 * ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p) ≤ y / 1000 := by
    rw [hxy, mul_pow]
    have hc : (0 : ℝ) < 1 - 2 * ((37 : ℕ) : ℝ) / 199 := by norm_num
    have hP' : ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p) ≤
        ((Fq 5 37 : ℚ) : ℝ) / (1 - 2 * ((37 : ℕ) : ℝ) / 199) := by
      rw [le_div_iff₀ hc]; exact h2
    have hF0 : 0 ≤ ((Fq 5 37 : ℚ) : ℝ) := le_trans (by positivity) (le_trans
      (mul_nonneg hP0 hc.le) h2)
    calc (14 / 25 : ℝ) ^ 37 * y ^ 37 * ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p)
        ≤ (14 / 25 : ℝ) ^ 37 * y * (((Fq 5 37 : ℚ) : ℝ) / (1 - 2 * ((37 : ℕ) : ℝ) / 199)) := by
          gcongr
      _ = y * (((14 / 25 : ℝ) ^ 37 * ((Fq 5 37 : ℚ) : ℝ)) /
            (1 - 2 * ((37 : ℕ) : ℝ) / 199)) := by ring
      _ ≤ y * ((1 / 1000 * (1 - 74 / 199)) / (1 - 2 * ((37 : ℕ) : ℝ) / 199)) := by
          gcongr
      _ = y / 1000 := by push_cast; field_simp; ring
  calc _ ≤ (n : ℝ) * x ^ 37 * ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p) := h1
    _ = n * (x ^ 37 * ∏ p ∈ primesIn 5 n, (1 + gm 37 p / p)) := by ring
    _ ≤ n * (y / 1000) := mul_le_mul_of_nonneg_left h4 hn
    _ = x * n / 560 := by rw [hy]; field_simp; ring

/-- **Paper Corollary 2.5(b), analytic part.** At most `n / 1000` integers `z ≤ n` satisfy
`∏_{p ∣ z, 11 ≤ p} (1 - 1/p) ≤ 3/4`. -/
theorem card_phi_eleven_le (n : ℕ) :
    (((Finset.Icc 1 n).filter (fun z => phiT (primesIn 11 n) z ≤ 3 / 4)).card : ℝ) ≤ n / 1000 := by
  have hT : ∀ p ∈ primesIn 11 n, p.Prime := fun p hp => (mem_primesIn.1 hp).2
  have h1 := card_phiT_le (primesIn 11 n) hT n 54 (x := 3 / 4) (by norm_num)
  have h2 := prod_primesIn_le 11 54 n (by norm_num)
  have h3 : ((3 / 4 : ℚ) : ℝ) ^ 54 * ((Fq 11 54 : ℚ) : ℝ) ≤
      ((1 / 1000 * (1 - 108 / 199) : ℚ) : ℝ) := by
    rw [← Rat.cast_pow, ← Rat.cast_mul]; exact_mod_cast Fq_eleven
  push_cast at h2 h3
  have hc : (0 : ℝ) < 1 - 2 * ((54 : ℕ) : ℝ) / 199 := by norm_num
  have hP' : ∏ p ∈ primesIn 11 n, (1 + gm 54 p / p) ≤
      ((Fq 11 54 : ℚ) : ℝ) / (1 - 2 * ((54 : ℕ) : ℝ) / 199) := by
    rw [le_div_iff₀ hc]; exact h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (3 / 4 : ℝ) ^ 54 * ∏ p ∈ primesIn 11 n, (1 + gm 54 p / p) ≤ 1 / 1000 := by
    calc (3 / 4 : ℝ) ^ 54 * ∏ p ∈ primesIn 11 n, (1 + gm 54 p / p)
        ≤ (3 / 4 : ℝ) ^ 54 * (((Fq 11 54 : ℚ) : ℝ) / (1 - 2 * ((54 : ℕ) : ℝ) / 199)) := by
          gcongr
      _ = ((3 / 4 : ℝ) ^ 54 * ((Fq 11 54 : ℚ) : ℝ)) / (1 - 2 * ((54 : ℕ) : ℝ) / 199) := by ring
      _ ≤ (1 / 1000 * (1 - 108 / 199)) / (1 - 2 * ((54 : ℕ) : ℝ) / 199) := by gcongr
      _ = 1 / 1000 := by push_cast; field_simp; ring
  calc _ ≤ (n : ℝ) * (3 / 4) ^ 54 * ∏ p ∈ primesIn 11 n, (1 + gm 54 p / p) := h1
    _ = n * ((3 / 4) ^ 54 * ∏ p ∈ primesIn 11 n, (1 + gm 54 p / p)) := by ring
    _ ≤ n * (1 / 1000) := mul_le_mul_of_nonneg_left h4 hn
    _ = n / 1000 := by ring

end ErdosSar
