import ErdosSar.HardCount
import ErdosSar.LargeN
import ErdosSar.OddCount
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Set-up for the proof of the main theorem

`NA n A m = N*(m) ∩ A`, the deficit `a(z) = |N*(z) \ A|`, undamaged numbers, and the numerical
estimates used in the construction of long cycles.
-/

namespace ErdosSar

open Finset

/-- `N*(m) ∩ A`. -/
def NA (n : ℕ) (A : Finset ℕ) (m : ℕ) : Finset ℕ := (Nstar n m).filter (· ∈ A)

/-- `a(z) = |N*(z) \ A|`: the neighbours of `z` in `E*(n)` that are missing from `A`. -/
def deficit (n : ℕ) (A : Finset ℕ) (z : ℕ) : ℕ := ((Nstar n z).filter (· ∉ A)).card

/-- `z` is undamaged if `a(z) ≤ (n/8) ρ'(z)`. -/
def Undamaged (n : ℕ) (A : Finset ℕ) (z : ℕ) : Prop := (deficit n A z : ℝ) ≤ n / 8 * rho z

noncomputable instance (n : ℕ) (A : Finset ℕ) : DecidablePred (Undamaged n A) :=
  fun z => by unfold Undamaged; infer_instance

theorem mem_Nstar {n m w : ℕ} : w ∈ Nstar n m ↔ w ∈ Estar n ∧ Nat.Coprime w m := by
  simp [Nstar]

theorem mem_Estar {n w : ℕ} : w ∈ Estar n ↔ (1 ≤ w ∧ w ≤ n) ∧ (w % 6 = 2 ∨ w % 6 = 4) := by
  simp [Estar]

theorem mem_NA {n : ℕ} {A : Finset ℕ} {m w : ℕ} : w ∈ NA n A m ↔ w ∈ Nstar n m ∧ w ∈ A := by
  simp [NA]

theorem even_of_mem_Estar {n w : ℕ} (h : w ∈ Estar n) : w % 2 = 0 := by
  have := (mem_Estar.1 h).2; omega

theorem coprime_of_mem_Nstar_lcm {n u v w : ℕ} (h : w ∈ Nstar n (Nat.lcm u v)) :
    Nat.Coprime w u ∧ Nat.Coprime w v := by
  have hc := (mem_Nstar.1 h).2
  exact ⟨Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_left u v) hc,
    Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_right u v) hc⟩

theorem deficit_le (n : ℕ) (A : Finset ℕ) (z : ℕ) : deficit n A z ≤ (Estar n \ A).card := by
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw
  exact Finset.mem_sdiff.2 ⟨(mem_Nstar.1 hw.1).1, hw.2⟩

theorem rho_pos (m : ℕ) : 0 < rho m :=
  lt_of_lt_of_le (by positivity) (rho_ge m)

theorem rho_le_of_dvd {z m : ℕ} (hzm : z ∣ m) (hm : m ≠ 0) : rho m ≤ rho z := by
  have hsub : bigPrimes z ⊆ bigPrimes m := by
    intro p hp
    obtain ⟨hpr, hpz, -, h5⟩ := mem_bigPrimes.1 hp
    exact mem_bigPrimes.2 ⟨hpr, dvd_trans hpz hzm, hm, h5⟩
  apply prod_le_prod_of_subset_unit hsub
  · intro p hp
    have : (1 : ℝ) ≤ p := by
      exact_mod_cast (show 1 ≤ p by have := (mem_bigPrimes.1 hp).2.2.2; omega)
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  · intro p hp
    have : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p by have := (mem_bigPrimes.1 hp).2.2.2; omega)
    have : 0 < 1 / (p : ℝ) := by positivity
    linarith

theorem odd_lcm {y z : ℕ} (hy : y % 2 = 1) (hz : z % 2 = 1) : Odd (Nat.lcm y z) := by
  have : Odd (y * z) := Nat.odd_mul.2 ⟨Nat.odd_iff.2 hy, Nat.odd_iff.2 hz⟩
  exact this.of_dvd_nat (Nat.lcm_dvd_mul y z)

theorem lcm_le_sq {n y z : ℕ} (hy : y ∈ Icc 1 n) (hz : z ∈ Icc 1 n) : Nat.lcm y z ≤ n ^ 2 := by
  obtain ⟨hy1, hyn⟩ := Finset.mem_Icc.1 hy
  obtain ⟨hz1, hzn⟩ := Finset.mem_Icc.1 hz
  calc Nat.lcm y z ≤ y * z := Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul y z)
    _ ≤ n * n := Nat.mul_le_mul hyn hzn
    _ = n ^ 2 := by ring

theorem lcm_ne_zero' {n y z : ℕ} (hy : y ∈ Icc 1 n) (hz : z ∈ Icc 1 n) : Nat.lcm y z ≠ 0 :=
  Nat.lcm_ne_zero (by have := (Finset.mem_Icc.1 hy).1; omega)
    (by have := (Finset.mem_Icc.1 hz).1; omega)

theorem card_Nstar_ge {n m : ℕ} (hm : Odd m) :
    (n : ℝ) / 3 * rho m - 2 ^ (bigPrimes m).card ≤ (Nstar n m).card := by
  have := abs_card_Nstar_sub_le (n := n) hm
  have := neg_abs_le ((Nstar n m).card - (n : ℝ) / 3 * rho m)
  linarith

/-- The uniform bound `1000 (K+1) 2^K ≤ n` in real form. -/
theorem large_n_real {n m : ℕ} (hn : N₀ ≤ n) (hm : m ≠ 0) (hmn : m ≤ n ^ 2) :
    (1000 : ℝ) * ((bigPrimes m).card + 1) * 2 ^ (bigPrimes m).card ≤ n := by
  exact_mod_cast large_n hn hm hmn

/-- **Connector bound.** For an easy `y` and an undamaged `z`, at least `2 + ρ'(z) n / 280`
elements of `A` are coprime to both. -/
theorem NA_card_master {n : ℕ} {A : Finset ℕ} {y z : ℕ} (hn : N₀ ≤ n) (hy : y ∈ Icc 1 n)
    (hz : z ∈ Icc 1 n) (hy2 : y % 2 = 1) (hz2 : z % 2 = 1) (hyE : 3 / 4 ≤ rho y)
    (hzU : Undamaged n A z) :
    2 + rho z * n / 280 ≤ ((NA n A (Nat.lcm y z)).card : ℝ) := by
  classical
  set m := Nat.lcm y z with hm
  have hm0 : m ≠ 0 := lcm_ne_zero' hy hz
  set K := (bigPrimes m).card with hK
  have hL := large_n_real hn hm0 (lcm_le_sq hy hz)
  rw [← hK] at hL
  have h1 := card_Nstar_ge (n := n) (odd_lcm hy2 hz2)
  rw [← hm, ← hK] at h1
  have hy0 : y ≠ 0 := by have := (Finset.mem_Icc.1 hy).1; omega
  have hz0 : z ≠ 0 := by have := (Finset.mem_Icc.1 hz).1; omega
  have h2 := rho_lcm_ge hy0 hz0
  rw [← hm] at h2
  have h3 := Finset.card_filter_add_card_filter_not (s := Nstar n m) (fun w => w ∈ A)
  have h4 : ((Nstar n m).filter (fun w => w ∉ A)).card ≤ deficit n A z := by
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    refine ⟨mem_Nstar.2 ⟨(mem_Nstar.1 hw.1).1, ?_⟩, hw.2⟩
    exact (coprime_of_mem_Nstar_lcm hw.1).2
  have h5 : (deficit n A z : ℝ) ≤ n / 8 * rho z := hzU
  have h6 : 1 / ((K : ℝ) + 1) ≤ rho m := rho_ge m
  have h7 : rho m ≤ rho z := rho_le_of_dvd (Nat.dvd_lcm_right y z) hm0
  have hNA : (NA n A m).card = ((Nstar n m).filter (fun w => w ∈ A)).card := rfl
  have h3' : ((NA n A m).card : ℝ) + ((Nstar n m).filter (fun w => w ∉ A)).card =
      (Nstar n m).card := by rw [hNA]; exact_mod_cast h3
  have h4' : (((Nstar n m).filter (fun w => w ∉ A)).card : ℝ) ≤ deficit n A z := by
    exact_mod_cast h4
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hrz : 1 ≤ rho z * (K + 1) := by
    have := h6.trans h7
    rw [div_le_iff₀ hK1] at this; linarith
  have hnr : (1000 : ℝ) * 2 ^ K ≤ n * rho z := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (1000 : ℝ) * (K + 1) * 2 ^ K ≤ n * rho z * (K + 1) := by nlinarith
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    nlinarith
  have hry : 3 / 4 * rho z ≤ rho m := by
    have := rho_nonneg z
    nlinarith
  have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrz0 := rho_nonneg z
  nlinarith

/-- `#{z ∈ H : ρ'(z) ≤ x} ≤ x n / 560` for `H ⊆ [1, n]` with `|H| ≤ n/1000`, all `x > 0`. -/
theorem card_filter_rho_le' {n : ℕ} {H : Finset ℕ} (hH : H ⊆ Icc 1 n)
    (hHc : (H.card : ℝ) ≤ n / 1000) {x : ℝ} (hx : 0 < x) :
    ((H.filter (fun z => rho z ≤ x)).card : ℝ) ≤ x * n / 560 := by
  rcases le_or_gt x (14 / 25) with hx1 | hx1
  · refine le_trans ?_ (card_rho_le n hx hx1)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hH)
  · have h1 : ((H.filter (fun z => rho z ≤ x)).card : ℝ) ≤ H.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

/-- **Degree bound.** If `ρ'(lcm(p, q)) ≥ 14/25`, then after removing the missing elements and
at most `n/500 + 2` further elements, `N*(lcm(p, q))` keeps at least `n/6 + 2` elements. -/
theorem deg_master {n : ℕ} {A : Finset ℕ} {p q : ℕ} (hn : N₀ ≤ n) (hp : p ∈ Icc 1 n)
    (hq : q ∈ Icc 1 n) (hp2 : p % 2 = 1) (hq2 : q % 2 = 1) (hrho : 14 / 25 ≤ rho (Nat.lcm p q))
    (hD : 70 * (Estar n \ A).card ≤ n) (W : Finset ℕ) (hW : (W.card : ℝ) ≤ n / 500 + 2) :
    n / 6 + 2 ≤ ((Nstar n (Nat.lcm p q)) \ ((Estar n \ A) ∪ W)).card := by
  set m := Nat.lcm p q with hm
  have hm0 : m ≠ 0 := lcm_ne_zero' hp hq
  set K := (bigPrimes m).card with hK
  have hL := large_n_real hn hm0 (lcm_le_sq hp hq)
  rw [← hK] at hL
  have h1 := card_Nstar_ge (n := n) (odd_lcm hp2 hq2)
  rw [← hm, ← hK] at h1
  have h2 := Finset.card_le_card_sdiff_add_card (s := Nstar n m) (t := (Estar n \ A) ∪ W)
  have h3 := Finset.card_union_le (Estar n \ A) W
  have h2' : ((Nstar n m).card : ℝ) ≤ ((Nstar n m) \ ((Estar n \ A) ∪ W)).card +
      (Estar n \ A).card + W.card := by
    have : (Nstar n m).card ≤ ((Nstar n m) \ ((Estar n \ A) ∪ W)).card +
        ((Estar n \ A).card + W.card) := by omega
    exact_mod_cast (by omega : (Nstar n m).card ≤ ((Nstar n m) \ ((Estar n \ A) ∪ W)).card +
        (Estar n \ A).card + W.card)
  have hD' : ((Estar n \ A).card : ℝ) ≤ n / 70 := by
    have : (70 : ℝ) * (Estar n \ A).card ≤ n := by exact_mod_cast hD
    linarith
  have hk : ((n / 6 + 2 : ℕ) : ℝ) ≤ (n : ℝ) / 6 + 2 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := 6)
    push_cast at this
    linarith
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2Kn : (1000 : ℝ) * 2 ^ K ≤ n := by nlinarith
  have hn0 : (100000 : ℝ) ≤ n := by
    have : (100000 : ℕ) ≤ n := le_trans (by unfold N₀; norm_num) hn
    exact_mod_cast this
  have hNm : (n : ℝ) / 3 * (14 / 25) ≤ (n : ℝ) / 3 * rho m :=
    mul_le_mul_of_nonneg_left hrho (by positivity)
  have : ((n / 6 + 2 : ℕ) : ℝ) ≤ ((Nstar n m \ (Estar n \ A ∪ W)).card : ℝ) := by
    linarith
  exact_mod_cast this

/-- At most `|D|` numbers in `O ⊆ [1, n]` are damaged. -/
theorem card_damaged_le {n : ℕ} {A O : Finset ℕ} (hO : O ⊆ Icc 1 n)
    (hD : 70 * (Estar n \ A).card ≤ n) :
    (O.filter (fun z => ¬ Undamaged n A z)).card ≤ (Estar n \ A).card := by
  classical
  set d := (Estar n \ A).card with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · have : O.filter (fun z => ¬ Undamaged n A z) = ∅ := by
      apply Finset.filter_false_of_mem
      intro z _ hz
      apply hz
      have := deficit_le n A z
      rw [← hd, hd0] at this
      have h0 : deficit n A z = 0 := by omega
      unfold Undamaged; rw [h0]; push_cast
      have := rho_nonneg z
      positivity
    rw [this]; simp
  · have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set x : ℝ := 8 * d / n with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x ≤ 14 / 25 := by
      rw [hx, div_le_iff₀ hnR]
      have : (70 : ℝ) * d ≤ n := by exact_mod_cast hD
      nlinarith
    have hsub : O.filter (fun z => ¬ Undamaged n A z) ⊆ (Icc 1 n).filter (fun z => rho z ≤ x) := by
      intro z hz
      obtain ⟨hzO, hz⟩ := Finset.mem_filter.1 hz
      refine Finset.mem_filter.2 ⟨hO hzO, ?_⟩
      unfold Undamaged at hz
      push Not at hz
      have h1 : (deficit n A z : ℝ) ≤ d := by exact_mod_cast deficit_le n A z
      rw [hx, le_div_iff₀ hnR]
      nlinarith
    have h1 := card_rho_le n hx0 hx1
    have h2 : ((O.filter (fun z => ¬ Undamaged n A z)).card : ℝ) ≤ d := by
      calc ((O.filter (fun z => ¬ Undamaged n A z)).card : ℝ)
          ≤ ((Icc 1 n).filter (fun z => rho z ≤ x)).card := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ x * n / 560 := h1
        _ = d / 70 := by rw [hx]; field_simp; ring
        _ ≤ d := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    exact_mod_cast h2

theorem phiT_primesIn_eleven {n z : ℕ} (hz1 : 1 ≤ z) (hzn : z ≤ n) (h5 : z % 5 ≠ 0)
    (h7 : z % 7 ≠ 0) : phiT (primesIn 11 n) z = rho z := by
  unfold phiT rho
  congr 1
  ext p
  rw [Finset.mem_filter, mem_primesIn, mem_bigPrimes]
  constructor
  · rintro ⟨⟨⟨h11, -⟩, hpr⟩, hpz⟩
    exact ⟨hpr, hpz, by omega, by omega⟩
  · rintro ⟨hpr, hpz, -, hp5⟩
    refine ⟨⟨⟨?_, (Nat.le_of_dvd (by omega) hpz).trans hzn⟩, hpr⟩, hpz⟩
    have hp5' : p ≠ 5 := by rintro rfl; omega
    have hp7' : p ≠ 7 := by rintro rfl; omega
    rcases (by omega : p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p ∨ p = 5 ∨ p = 7) with
      h | h | h | h | h | h | h
    · subst h; exact absurd hpr (by decide)
    · subst h; exact absurd hpr (by decide)
    · subst h; exact absurd hpr (by decide)
    · subst h; exact absurd hpr (by decide)
    · exact h
    · exact absurd h hp5'
    · exact absurd h hp7'

/-- **Paper Corollary 2.5(b).** Few odd numbers are not easy. -/
theorem card_nonEasy_le (n : ℕ) :
    (((Icc 1 n).filter (fun z => z % 2 = 1 ∧ rho z < 3 / 4)).card : ℝ) ≤
      11 * ((n / 70 + 1 : ℕ) : ℝ) + n / 1000 := by
  classical
  have hsub : (Icc 1 n).filter (fun z => z % 2 = 1 ∧ rho z < 3 / 4) ⊆
      (Icc 1 n).filter FiveSeven ∪ (Icc 1 n).filter (fun z => phiT (primesIn 11 n) z ≤ 3 / 4) := by
    intro z hz
    obtain ⟨hzI, hz2, hzr⟩ := Finset.mem_filter.1 hz
    obtain ⟨hz1, hzn⟩ := Finset.mem_Icc.1 hzI
    by_cases h57 : z % 5 = 0 ∨ z % 7 = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hzI, hz2, h57⟩)
    · push Not at h57
      refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzI, ?_⟩)
      rw [phiT_primesIn_eleven hz1 hzn h57.1 h57.2]
      exact hzr.le
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Icc 1 n).filter FiveSeven)
    ((Icc 1 n).filter (fun z => phiT (primesIn 11 n) z ≤ 3 / 4))
  have h3 := card_fiveSeven_le n
  have h4 := card_phi_eleven_le n
  have h5 : (((Icc 1 n).filter (fun z => z % 2 = 1 ∧ rho z < 3 / 4)).card : ℝ) ≤
      ((Icc 1 n).filter FiveSeven).card +
        ((Icc 1 n).filter (fun z => phiT (primesIn 11 n) z ≤ 3 / 4)).card := by
    exact_mod_cast h1.trans h2
  have h3' : (((Icc 1 n).filter FiveSeven).card : ℝ) ≤ 11 * ((n / 70 + 1 : ℕ) : ℝ) := by
    exact_mod_cast h3
  linarith

end ErdosSar
