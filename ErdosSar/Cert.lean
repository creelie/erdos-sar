import ErdosSar.CountingR
import ErdosSar.HardCount
import ErdosSar.Numerics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Density certificates in residue classes

For a set `R` of residues mod 6 closed under negation and a threshold `θ`, we bound
`#{z ≤ n : z mod 6 ∈ R, ρ'(z) < θ}` by `(n/6) |R| β` with an explicit rational `β`.

The primes `p ≥ 5` dividing `z` are split into three ranges.
* The small primes `P` (in practice `5 ≤ p ≤ 19`) are treated exactly: `z` is sorted by its
  *signature* `S = {p ∈ P : p ∣ z}`, and the number of `z` with a given signature and a given
  further divisor is an exact count `CntR` in a residue class.
* The middle primes `T'` (in practice `23 ≤ p ≤ Y`) are controlled by the moment method
  (Rankin's trick) inside each signature class.
* The large primes `p > Y` are controlled by a first-moment (Markov) bound for
  `∑_{p ∣ z, p > Y} 1/p`, using `∏ (1 - 1/p) ≥ 1 - ∑ 1/p`.
-/

namespace ErdosSar

open Finset

/-! ### Elementary inequalities -/

theorem one_sub_sum_le_prod (F : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ p ∈ F, 0 ≤ a p)
    (h1 : ∀ p ∈ F, a p ≤ 1) : 1 - ∑ p ∈ F, a p ≤ ∏ p ∈ F, (1 - a p) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    have ih' := ih (fun p hp => h0 p (mem_insert_of_mem hp))
      (fun p hp => h1 p (mem_insert_of_mem hp))
    have hq0 := h0 q (mem_insert_self q s)
    have hq1 := h1 q (mem_insert_self q s)
    have hs0 : 0 ≤ ∑ p ∈ s, a p := sum_nonneg fun p hp => h0 p (mem_insert_of_mem hp)
    have h2 : (1 - a q) * (1 - ∑ p ∈ s, a p) ≤ (1 - a q) * ∏ p ∈ s, (1 - a p) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    nlinarith [mul_nonneg hq0 hs0]

theorem sum_Ico_telescope_gen (Y : ℕ) (hY : 2 ≤ Y) (k : ℕ) :
    ∑ p ∈ Finset.Ico Y (Y + k), (1 / ((p : ℝ) - 1) - 1 / p) =
      1 / ((Y : ℝ) - 1) - 1 / ((Y : ℝ) - 1 + k) := by
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show Y + (k + 1) = (Y + k) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (Y : ℝ) - 1 + k ≠ 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h2 : (Y : ℝ) + k ≠ 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h3 : (Y : ℝ) - 1 + (k + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [show (Y : ℝ) + k - 1 = (Y : ℝ) - 1 + k by ring,
      show (Y : ℝ) - 1 + (k + 1) = (Y : ℝ) + k by ring]
    ring

/-- `∑_{p ∈ T} 1/p² ≤ 1/(Y - 1)` for a finite set `T` of integers `≥ Y ≥ 2`. -/
theorem sum_inv_sq_le_gen (Y : ℕ) (hY : 2 ≤ Y) (T : Finset ℕ) (hT : ∀ p ∈ T, Y ≤ p) :
    ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ 1 / ((Y : ℝ) - 1) := by
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  set k := T.sup id + 1
  have hsub : T ⊆ Finset.Ico Y (Y + k) := fun p hp =>
    Finset.mem_Ico.2 ⟨hT p hp, by
      have : p ≤ T.sup id := Finset.le_sup (f := id) hp
      omega⟩
  have hterm : ∀ p ∈ Finset.Ico Y (Y + k), 1 / ((p : ℝ) ^ 2) ≤ 1 / ((p : ℝ) - 1) - 1 / p := by
    intro p hp
    have hYp : (Y : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Ico.1 hp).1
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
  have hnn : ∀ p ∈ Finset.Ico Y (Y + k), p ∉ T → 0 ≤ 1 / ((p : ℝ) - 1) - 1 / p := by
    intro p hp _
    have := hterm p hp
    have : 0 ≤ 1 / ((p : ℝ) ^ 2) := by positivity
    linarith
  calc ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ ∑ p ∈ T, (1 / ((p : ℝ) - 1) - 1 / p) :=
        Finset.sum_le_sum fun p hp => hterm p (hsub hp)
    _ ≤ ∑ p ∈ Finset.Ico Y (Y + k), (1 / ((p : ℝ) - 1) - 1 / p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = 1 / ((Y : ℝ) - 1) - 1 / ((Y : ℝ) - 1 + k) := sum_Ico_telescope_gen Y hY k
    _ ≤ 1 / ((Y : ℝ) - 1) := by
        have : 0 ≤ 1 / ((Y : ℝ) - 1 + k) := by
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          apply div_nonneg zero_le_one; linarith
        linarith

/-! ### Large primes: a first-moment bound -/

/-- **Markov bound.** At most `n / (η (Y - 1))` integers `z ≤ n` have
`∑_{p ∈ Big, p ∣ z} 1/p > η`, if all elements of `Big` are `≥ Y ≥ 2`. -/
theorem card_markov (Y : ℕ) (hY : 2 ≤ Y) (Big : Finset ℕ) (hBig : ∀ p ∈ Big, Y ≤ p) (n : ℕ)
    {η : ℝ} (hη : 0 < η) :
    (((Icc 1 n).filter (fun z => η < ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ))).card : ℝ) ≤
      n / (η * ((Y : ℝ) - 1)) := by
  set S := (Icc 1 n).filter (fun z => η < ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ))
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hpos : ∀ p ∈ Big, (0 : ℝ) < p := fun p hp => by
    have : (Y : ℝ) ≤ p := by exact_mod_cast hBig p hp
    linarith
  have h1 : (S.card : ℝ) * η ≤ ∑ z ∈ S, ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun z hz => (Finset.mem_filter.1 hz).2.le
  have h2 : ∑ z ∈ S, ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ) ≤
      ∑ z ∈ Icc 1 n, ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro z _ _
    exact Finset.sum_nonneg fun p hp => by
      have := hpos p (Finset.mem_filter.1 hp).1; positivity
  have h3 : ∑ z ∈ Icc 1 n, ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ) =
      ∑ p ∈ Big, ((n / p : ℕ) : ℝ) * (1 / (p : ℝ)) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_dvd_Icc n p (by have := hBig p hp; omega)]
  have h4 : ∑ p ∈ Big, ((n / p : ℕ) : ℝ) * (1 / (p : ℝ)) ≤ ∑ p ∈ Big, n * (1 / ((p : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp0 := hpos p hp
    have : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := Nat.cast_div_le
    calc ((n / p : ℕ) : ℝ) * (1 / (p : ℝ)) ≤ (n : ℝ) / p * (1 / (p : ℝ)) := by gcongr
      _ = n * (1 / ((p : ℝ) ^ 2)) := by field_simp
  have h5 : ∑ p ∈ Big, (n : ℝ) * (1 / ((p : ℝ) ^ 2)) ≤ n * (1 / ((Y : ℝ) - 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_le_gen Y hY Big hBig) (Nat.cast_nonneg n)
  have hY1 : (0 : ℝ) < (Y : ℝ) - 1 := by linarith
  rw [le_div_iff₀ (by positivity)]
  calc (S.card : ℝ) * (η * ((Y : ℝ) - 1)) = (S.card * η) * ((Y : ℝ) - 1) := by ring
    _ ≤ (n * (1 / ((Y : ℝ) - 1))) * ((Y : ℝ) - 1) := by
        apply mul_le_mul_of_nonneg_right _ hY1.le
        linarith
    _ = n := by field_simp

/-! ### Exact counts in a residue class with prescribed prime divisors -/

theorem mod_six_of_prime_ge_five {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h; omega
  omega

theorem prod_mod_six (M : Finset ℕ) (hM : ∀ p ∈ M, p % 6 = 1 ∨ p % 6 = 5) :
    (∏ p ∈ M, p) % 6 = 1 ∨ (∏ p ∈ M, p) % 6 = 5 := by
  induction M using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, Nat.mul_mod]
    have hq6 := hM q (mem_insert_self q s)
    have ih' := ih (fun p hp => hM p (mem_insert_of_mem hp))
    rcases hq6 with h | h <;> rcases ih' with h' | h' <;> rw [h, h'] <;> norm_num

/-- The number of `z ≤ n` with `z mod 6 ∈ R`, divisible by every prime of `M` and by no prime
of `P'` (where `M`, `P'` are disjoint sets of primes `≥ 5`) is `CntR (n / ∏ M) R P'`. -/
theorem card_class_dvd_ndvd {R : Finset ℕ} (hR : SymRes R) (M P' : Finset ℕ)
    (hM : ∀ p ∈ M, p.Prime ∧ 5 ≤ p) (hP' : ∀ p ∈ P', p.Prime) (hdisj : Disjoint M P') (n : ℕ) :
    ((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ (∀ p ∈ M, p ∣ z) ∧ ∀ p ∈ P', ¬ p ∣ z)).card =
      CntR (n / ∏ p ∈ M, p) R P' := by
  set q := ∏ p ∈ M, p with hq
  have hq0 : 0 < q := Finset.prod_pos fun p hp => (hM p hp).1.pos
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 :=
    prod_mod_six M (fun p hp => mod_six_of_prime_ge_five (hM p hp).1 (hM p hp).2)
  have hdvd : ∀ z, (∀ p ∈ M, p ∣ z) ↔ q ∣ z := by
    intro z
    constructor
    · intro h
      exact Finset.prod_primes_dvd z (fun p hp => (hM p hp).1.prime) h
    · intro h p hp
      exact dvd_trans (Finset.dvd_prod_of_mem _ hp) h
  have hnot : ∀ p ∈ P', ¬ p ∣ q := by
    intro p hp hpq
    rw [hq, Prime.dvd_finsetProd_iff (hP' p hp).prime] at hpq
    obtain ⟨p', hp', hpp'⟩ := hpq
    have := (Nat.prime_dvd_prime_iff_eq (hP' p hp) (hM p' hp').1).1 hpp'
    subst this
    exact Finset.disjoint_left.1 hdisj hp' hp
  unfold CntR
  rw [← Finset.card_image_of_injective ((Icc 1 (n / q)).filter
    (fun w => w % 6 ∈ R ∧ ∀ p ∈ P', ¬ p ∣ w)) (fun a b h => Nat.eq_of_mul_eq_mul_left hq0 h :
    Function.Injective (fun j => q * j))]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hz1, hzn⟩, hzR, hzM, hzP⟩
    obtain ⟨j, rfl⟩ := (hdvd z).1 hzM
    refine ⟨j, ⟨⟨?_, ?_⟩, (mul_mod_mem_iff hR hq6 j).1 hzR, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hz1
      · exact h
    · rw [Nat.le_div_iff_mul_le hq0]; linarith [Nat.mul_comm q j]
    · intro p hp hpj
      exact hzP p hp (Dvd.dvd.mul_left hpj q)
  · rintro ⟨j, ⟨⟨hj1, hjn⟩, hjR, hjP⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hq0 hj1, ?_⟩, (mul_mod_mem_iff hR hq6 j).2 hjR, (hdvd _).2 (Dvd.intro j rfl),
      ?_⟩
    · rw [Nat.le_div_iff_mul_le hq0] at hjn; linarith [Nat.mul_comm q j]
    · intro p hp hpqj
      rcases (Nat.Prime.dvd_mul (hP' p hp)).1 hpqj with h | h
      · exact hnot p hp h
      · exact hjP p hp h

/-! ### Signature classes and Rankin's trick inside them -/

/-- The `z ∈ [1, n]` with `z mod 6 ∈ R` whose set of prime divisors in `P` is exactly `S`. -/
def Zset (n : ℕ) (R P S : Finset ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun z => z % 6 ∈ R ∧ P.filter (· ∣ z) = S)

/-- The relative density `∏_{p ∈ P \ S} (1 - 1/p) / ∏_{p ∈ S} p` of the signature `S`. -/
noncomputable def dens (P S : Finset ℕ) : ℝ := (∏ p ∈ P \ S, (1 - 1 / (p : ℝ))) / ∏ p ∈ S, (p : ℝ)

/-- `ρ'` of a signature: `∏_{p ∈ S} (1 - 1/p)`. -/
noncomputable def rhoS (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 - 1 / (p : ℝ))

theorem filter_dvd_eq_iff {P S : Finset ℕ} (hSP : S ⊆ P) (z : ℕ) :
    P.filter (· ∣ z) = S ↔ (∀ p ∈ S, p ∣ z) ∧ ∀ p ∈ P \ S, ¬ p ∣ z := by
  constructor
  · rintro rfl
    refine ⟨fun p hp => (Finset.mem_filter.1 hp).2, fun p hp hpz => ?_⟩
    obtain ⟨hpP, hpS⟩ := Finset.mem_sdiff.1 hp
    exact hpS (Finset.mem_filter.2 ⟨hpP, hpz⟩)
  · rintro ⟨h1, h2⟩
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpP, hpz⟩
      by_contra hpS
      exact h2 p (Finset.mem_sdiff.2 ⟨hpP, hpS⟩) hpz
    · intro hpS
      exact ⟨hSP hpS, h1 p hpS⟩

theorem card_Zset_dvd {R : Finset ℕ} (hR : SymRes R) {P S T' D : Finset ℕ} (hSP : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hT : ∀ p ∈ T', p.Prime ∧ 5 ≤ p) (hPT : Disjoint P T')
    (hD : D ⊆ T') (n : ℕ) :
    ((Zset n R P S).filter (fun z => ∀ p ∈ D, p ∣ z)).card =
      CntR (n / ∏ p ∈ S ∪ D, p) R (P \ S) := by
  rw [← card_class_dvd_ndvd hR (S ∪ D) (P \ S)
    (fun p hp => by
      rcases Finset.mem_union.1 hp with h | h
      · exact hP p (hSP h)
      · exact hT p (hD h))
    (fun p hp => (hP p (Finset.mem_sdiff.1 hp).1).1)
    (by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_sdiff, Finset.disjoint_of_subset_left hD
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hPT.symm)⟩) n]
  congr 1
  ext z
  simp only [Zset, Finset.mem_filter, Finset.mem_union, filter_dvd_eq_iff hSP]
  constructor
  · rintro ⟨⟨hz, hzR, hzS, hzP⟩, hzD⟩
    exact ⟨hz, hzR, fun p hp => hp.elim (hzS p) (hzD p), hzP⟩
  · rintro ⟨hz, hzR, hzSD, hzP⟩
    exact ⟨⟨hz, hzR, fun p hp => hzSD p (Or.inl hp), hzP⟩, fun p hp => hzSD p (Or.inr hp)⟩

theorem CntR_le_main {R : Finset ℕ} (hR : SymRes R) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (N : ℕ) :
    (CntR N R P : ℝ) ≤ (N : ℝ) / 6 * R.card * ∏ p ∈ P, (1 - 1 / (p : ℝ)) + R.card * 2 ^ P.card := by
  have h := abs_CntR_sub_mainTermR_le hR P
    (fun p hp => mod_six_of_prime_ge_five (hP p hp).1 (hP p hp).2)
    (fun p hp q hq hpq => (Nat.coprime_primes (hP p hp).1 (hP q hq).1).2 hpq) N
  unfold mainTermR at h
  have := le_abs_self ((CntR N R P : ℝ) - (N : ℝ) / 6 * R.card * ∏ p ∈ P, (1 - 1 / (p : ℝ)))
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  nlinarith

theorem card_Zset_dvd_le {R : Finset ℕ} (hR : SymRes R) {P S T' D : Finset ℕ} (hSP : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hT : ∀ p ∈ T', p.Prime ∧ 5 ≤ p) (hPT : Disjoint P T')
    (hD : D ⊆ T') (n : ℕ) :
    (((Zset n R P S).filter (fun z => ∀ p ∈ D, p ∣ z)).card : ℝ) ≤
      (n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ D, (1 / (p : ℝ)) + R.card * 2 ^ P.card := by
  rw [card_Zset_dvd hR hSP hP hT hPT hD n]
  have hSD : Disjoint S D :=
    Finset.disjoint_of_subset_left hSP (Finset.disjoint_of_subset_right hD hPT)
  have h1 := CntR_le_main hR (P \ S) (fun p hp => hP p (Finset.mem_sdiff.1 hp).1)
    (n / ∏ p ∈ S ∪ D, p)
  have hpos : ∀ p ∈ S ∪ D, (0 : ℝ) < p := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact_mod_cast (hP p (hSP h)).1.pos
    · exact_mod_cast (hT p (hD h)).1.pos
  have hN : ((n / ∏ p ∈ S ∪ D, p : ℕ) : ℝ) ≤ (n : ℝ) / ((∏ p ∈ S, (p : ℝ)) * ∏ p ∈ D, (p : ℝ)) := by
    rw [← Finset.prod_union hSD]
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := ∏ p ∈ S ∪ D, p)
    push_cast at this
    exact this
  have hcard : (P \ S).card ≤ P.card := Finset.card_le_card Finset.sdiff_subset
  have h2 : (2 : ℝ) ^ (P \ S).card ≤ 2 ^ P.card := pow_le_pow_right₀ (by norm_num) hcard
  have hprod0 : 0 ≤ ∏ p ∈ P \ S, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p hp => by
    have : (5 : ℝ) ≤ p := by exact_mod_cast (hP p (Finset.mem_sdiff.1 hp).1).2
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hS0 : 0 < ∏ p ∈ S, (p : ℝ) := Finset.prod_pos fun p hp => hpos p (Finset.mem_union_left _ hp)
  have hD0 : 0 < ∏ p ∈ D, (p : ℝ) := Finset.prod_pos fun p hp => hpos p (Finset.mem_union_right _ hp)
  have e : (n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ D, (1 / (p : ℝ)) =
      (n : ℝ) / ((∏ p ∈ S, (p : ℝ)) * ∏ p ∈ D, (p : ℝ)) / 6 * R.card *
        ∏ p ∈ P \ S, (1 - 1 / (p : ℝ)) := by
    unfold dens
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    field_simp
  rw [e]
  have h3 : ((n / ∏ p ∈ S ∪ D, p : ℕ) : ℝ) / 6 * R.card * ∏ p ∈ P \ S, (1 - 1 / (p : ℝ)) ≤
      (n : ℝ) / ((∏ p ∈ S, (p : ℝ)) * ∏ p ∈ D, (p : ℝ)) / 6 * R.card *
        ∏ p ∈ P \ S, (1 - 1 / (p : ℝ)) := by gcongr
  have h4 : (R.card : ℝ) * 2 ^ (P \ S).card ≤ R.card * 2 ^ P.card :=
    mul_le_mul_of_nonneg_left h2 hR0
  linarith

/-- **Rankin's trick in a signature class.** -/
theorem sum_Zset_prod_le {R : Finset ℕ} (hR : SymRes R) {P S T' : Finset ℕ} (hSP : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hT : ∀ p ∈ T', p.Prime ∧ 5 ≤ p) (hPT : Disjoint P T')
    (g : ℕ → ℝ) (hg : ∀ p ∈ T', 0 ≤ g p) (n : ℕ) :
    ∑ z ∈ Zset n R P S, ∏ p ∈ T'.filter (· ∣ z), (1 + g p) ≤
      (n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ T', (1 + g p / p) +
        R.card * 2 ^ P.card * ∏ p ∈ T', (1 + g p) := by
  have key : ∀ z, ∏ p ∈ T'.filter (· ∣ z), (1 + g p) =
      ∑ D ∈ T'.powerset, if (∀ p ∈ D, p ∣ z) then ∏ p ∈ D, g p else 0 := by
    intro z
    rw [Finset.prod_filter]
    have : ∀ p ∈ T', (if p ∣ z then 1 + g p else 1) = 1 + (if p ∣ z then g p else 0) := by
      intro p _; split_ifs <;> ring
    rw [Finset.prod_congr rfl this, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro D _
    rw [Finset.prod_ite_zero]
  simp_rw [key]
  rw [Finset.sum_comm]
  have hterm : ∀ D ∈ T'.powerset,
      ∑ z ∈ Zset n R P S, (if (∀ p ∈ D, p ∣ z) then ∏ p ∈ D, g p else 0) ≤
        (∏ p ∈ D, g p) * ((n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ D, (1 / (p : ℝ)) +
          R.card * 2 ^ P.card) := by
    intro D hD
    have hDT := Finset.mem_powerset.1 hD
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hg0 : 0 ≤ ∏ p ∈ D, g p := Finset.prod_nonneg fun p hp => hg p (hDT hp)
    exact mul_le_mul_of_nonneg_left (card_Zset_dvd_le hR hSP hP hT hPT hDT n) hg0
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  have e1 : ∀ D ∈ T'.powerset, (∏ p ∈ D, g p) * ((n : ℝ) / 6 * R.card * dens P S *
      ∏ p ∈ D, (1 / (p : ℝ)) + R.card * 2 ^ P.card) =
      (n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ D, (g p / p) +
        R.card * 2 ^ P.card * ∏ p ∈ D, g p := by
    intro D _
    have : ∏ p ∈ D, (g p / p) = (∏ p ∈ D, g p) * ∏ p ∈ D, (1 / (p : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => by ring
    rw [this]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.prod_one_add, ← Finset.prod_one_add]

/-- **Moment bound in a signature class.** -/
theorem card_Zset_phiT_le {R : Finset ℕ} (hR : SymRes R) {P S T' : Finset ℕ} (hSP : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hT : ∀ p ∈ T', p.Prime ∧ 5 ≤ p) (hPT : Disjoint P T')
    (n m : ℕ) {t : ℝ} (ht : 0 < t) :
    (((Zset n R P S).filter (fun z => phiT T' z ≤ t)).card : ℝ) ≤
      t ^ m * ((n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ T', (1 + gm m p / p) +
        R.card * 2 ^ P.card * ∏ p ∈ T', (1 + gm m p)) := by
  have hTp : ∀ p ∈ T', p.Prime := fun p hp => (hT p hp).1
  set Z := (Zset n R P S).filter (fun z => phiT T' z ≤ t)
  have h1 : ∀ z ∈ Z, 1 ≤ t ^ m * ((phiT T' z)⁻¹) ^ m := by
    intro z hz
    have hz' := (Finset.mem_filter.1 hz).2
    have hpos := phiT_pos T' hTp z
    rw [← mul_pow]
    apply one_le_pow₀
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]; exact hz'
  have h2 : (Z.card : ℝ) ≤ ∑ z ∈ Z, t ^ m * ((phiT T' z)⁻¹) ^ m := by
    have := Finset.sum_le_sum h1
    simpa using this
  have h3 : ∑ z ∈ Z, t ^ m * ((phiT T' z)⁻¹) ^ m ≤
      ∑ z ∈ Zset n R P S, t ^ m * ((phiT T' z)⁻¹) ^ m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro z _ _
    have := phiT_pos T' hTp z
    positivity
  have h4 := sum_Zset_prod_le hR hSP hP hT hPT (gm m) (fun p hp => gm_nonneg m p (hTp p hp).two_le) n
  have h5 : ∑ z ∈ Zset n R P S, t ^ m * ((phiT T' z)⁻¹) ^ m =
      t ^ m * ∑ z ∈ Zset n R P S, ∏ p ∈ T'.filter (· ∣ z), (1 + gm m p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [inv_phiT_pow T' hTp]
  have htm : 0 ≤ t ^ m := pow_nonneg ht.le m
  calc (Z.card : ℝ) ≤ _ := h2
    _ ≤ _ := h3
    _ = _ := h5
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 htm

/-! ### Splitting `ρ'` into small, middle and large primes -/

/-- The small primes `5 ≤ p ≤ 19`. -/
def P19 : Finset ℕ := {5, 7, 11, 13, 17, 19}

theorem mem_P19 {p : ℕ} : p ∈ P19 ↔ (5 ≤ p ∧ p ≤ 19) ∧ p.Prime := by
  constructor
  · intro h
    simp only [P19, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rintro ⟨⟨h5, h19⟩, hp⟩
    simp only [P19, Finset.mem_insert, Finset.mem_singleton]
    interval_cases p <;> simp_all <;> norm_num at hp

theorem P19_prime : ∀ p ∈ P19, p.Prime ∧ 5 ≤ p := fun p hp => ⟨(mem_P19.1 hp).2, (mem_P19.1 hp).1.1⟩

theorem primesIn_prime {s n : ℕ} (hs : 5 ≤ s) : ∀ p ∈ primesIn s n, p.Prime ∧ 5 ≤ p :=
  fun p hp => ⟨(mem_primesIn.1 hp).2, le_trans hs (mem_primesIn.1 hp).1.1⟩

theorem disjoint_P19 (Y : ℕ) : Disjoint P19 (primesIn 23 Y) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have := (mem_P19.1 hp).1.2
  have := (mem_primesIn.1 hp').1.1
  omega

theorem rhoS_pos {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) : 0 < rhoS S :=
  Finset.prod_pos fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith

/-- `ρ'(z) = ρ'(S) φ_{T'}(z) φ_{Big}(z)` with `S` the signature of `z` on `P19`,
`T'` the primes in `[23, Y]` and `Big` the primes in `[Y + 1, n]`. -/
theorem rho_split {n z : ℕ} (hz1 : 1 ≤ z) (hzn : z ≤ n) (Y : ℕ) (hY : 19 ≤ Y) :
    rho z = rhoS (P19.filter (· ∣ z)) * phiT (primesIn 23 Y) z * phiT (primesIn (Y + 1) n) z := by
  unfold rho rhoS phiT
  have hsplit : bigPrimes z = (P19.filter (· ∣ z) ∪ (primesIn 23 Y).filter (· ∣ z)) ∪
      (primesIn (Y + 1) n).filter (· ∣ z) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, mem_bigPrimes, mem_P19, mem_primesIn]
    constructor
    · rintro ⟨hp, hpz, -, h5⟩
      have hpn : p ≤ n := (Nat.le_of_dvd (by omega) hpz).trans hzn
      by_cases h19 : p ≤ 19
      · exact Or.inl (Or.inl ⟨⟨⟨h5, h19⟩, hp⟩, hpz⟩)
      · by_cases hYp : p ≤ Y
        · refine Or.inl (Or.inr ⟨⟨⟨?_, hYp⟩, hp⟩, hpz⟩)
          by_contra h23
          interval_cases p <;> norm_num at hp
        · exact Or.inr ⟨⟨⟨by omega, hpn⟩, hp⟩, hpz⟩
    · rintro ((⟨⟨⟨h5, -⟩, hp⟩, hpz⟩ | ⟨⟨⟨h23, -⟩, hp⟩, hpz⟩) | ⟨⟨⟨hY1, -⟩, hp⟩, hpz⟩)
      · exact ⟨hp, hpz, by omega, h5⟩
      · exact ⟨hp, hpz, by omega, by omega⟩
      · exact ⟨hp, hpz, by omega, by omega⟩
  have hd1 : Disjoint (P19.filter (· ∣ z)) ((primesIn 23 Y).filter (· ∣ z)) :=
    Finset.disjoint_filter_filter (disjoint_P19 Y)
  have hd2 : Disjoint (P19.filter (· ∣ z) ∪ (primesIn 23 Y).filter (· ∣ z))
      ((primesIn (Y + 1) n).filter (· ∣ z)) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      intro p hp hp'
      have := (mem_P19.1 (Finset.mem_filter.1 hp).1).1.2
      have := (mem_primesIn.1 (Finset.mem_filter.1 hp').1).1.1
      omega
    · rw [Finset.disjoint_left]
      intro p hp hp'
      have := (mem_primesIn.1 (Finset.mem_filter.1 hp).1).1.2
      have := (mem_primesIn.1 (Finset.mem_filter.1 hp').1).1.1
      omega
  rw [hsplit, Finset.prod_union hd2, Finset.prod_union hd1]

/-! ### The combined bound -/


/-- **Bad numbers in a residue class** (general prime sets). If `ρ' = ρ'(S) φ_{T'} φ_{Big}` on
`[1, n]` and `θ ≤ θ' (1 - η)`, the number of `z ≤ n` with `z mod 6 ∈ R` and `ρ'(z) < θ` is at most
the Markov term plus, for every signature `S`, the moment bound with an exponent `mS S`. -/
theorem card_bad_le_gen {R : Finset ℕ} (hR : SymRes R) {θ θ' η : ℝ} (hθ : 0 < θ) (hη0 : 0 < η)
    (hη1 : η < 1) (hθθ' : θ ≤ θ' * (1 - η)) (P T' Big : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p) (hT : ∀ p ∈ T', p.Prime ∧ 5 ≤ p) (hPT : Disjoint P T')
    (Y : ℕ) (hY : 1 ≤ Y) (hBig : ∀ p ∈ Big, Y + 1 ≤ p) (n : ℕ)
    (hsplit : ∀ z, 1 ≤ z → z ≤ n → rho z = rhoS (P.filter (· ∣ z)) * phiT T' z * phiT Big z)
    (mS : Finset ℕ → ℕ) :
    (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ) ≤
      n / (η * Y) + ∑ S ∈ P.powerset, (θ' / rhoS S) ^ mS S *
        ((n : ℝ) / 6 * R.card * dens P S * ∏ p ∈ T', (1 + gm (mS S) p / p) +
          R.card * 2 ^ P.card * ∏ p ∈ T', (1 + gm (mS S) p)) := by
  set Mk := (Icc 1 n).filter (fun z => η < ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ)) with hMk
  have hθ' : 0 < θ' := by
    by_contra h
    push Not at h
    have : θ' * (1 - η) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  have hsub : (Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ) ⊆
      Mk ∪ P.powerset.biUnion
        (fun S => (Zset n R P S).filter (fun z => phiT T' z ≤ θ' / rhoS S)) := by
    intro z hz
    obtain ⟨hzI, hzR, hzθ⟩ := Finset.mem_filter.1 hz
    obtain ⟨hz1, hzn⟩ := Finset.mem_Icc.1 hzI
    by_cases hM : z ∈ Mk
    · exact Finset.mem_union_left _ hM
    · apply Finset.mem_union_right
      have hsum : ∑ p ∈ Big.filter (· ∣ z), 1 / (p : ℝ) ≤ η := by
        by_contra h
        push Not at h
        exact hM (Finset.mem_filter.2 ⟨hzI, h⟩)
      have hBig1 : 1 - η ≤ phiT Big z := by
        unfold phiT
        have hp2 : ∀ p ∈ Big.filter (· ∣ z), (2 : ℝ) ≤ p := fun p hp => by
          have := hBig p (Finset.mem_filter.1 hp).1
          exact_mod_cast (show 2 ≤ p by omega)
        have := one_sub_sum_le_prod (Big.filter (· ∣ z)) (fun p => 1 / (p : ℝ))
          (fun p hp => by have := hp2 p hp; positivity)
          (fun p hp => by have := hp2 p hp; rw [div_le_one (by linarith)]; linarith)
        linarith
      set S := P.filter (· ∣ z) with hSdef
      have hS : S ∈ P.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
      refine Finset.mem_biUnion.2 ⟨S, hS, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzI, hzR, rfl⟩,
        ?_⟩⟩
      have hs := hsplit z hz1 hzn
      have hrS : 0 < rhoS S := rhoS_pos fun p hp => (hP p (Finset.mem_filter.1 hp).1).1.two_le
      have hT0 : 0 < phiT T' z := phiT_pos T' (fun p hp => (hT p hp).1) z
      rw [le_div_iff₀ hrS]
      have h1 : rhoS S * phiT T' z * (1 - η) ≤ rho z := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left hBig1 (by positivity)
      have h2 : rhoS S * phiT T' z * (1 - η) < θ' * (1 - η) := by linarith
      have h3 : rhoS S * phiT T' z < θ' := lt_of_mul_lt_mul_right h2 (by linarith)
      linarith
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard2 := Finset.card_biUnion_le (s := P.powerset)
    (t := fun S => (Zset n R P S).filter (fun z => phiT T' z ≤ θ' / rhoS S))
  have hMk' : (Mk.card : ℝ) ≤ n / (η * Y) := by
    have := card_markov (Y + 1) (by omega) Big hBig n hη0
    have e : ((Y + 1 : ℕ) : ℝ) - 1 = Y := by push_cast; ring
    rw [e] at this
    exact this
  have hS : ∀ S ∈ P.powerset,
      (((Zset n R P S).filter (fun z => phiT T' z ≤ θ' / rhoS S)).card : ℝ) ≤
        (θ' / rhoS S) ^ mS S * ((n : ℝ) / 6 * R.card * dens P S *
          ∏ p ∈ T', (1 + gm (mS S) p / p) + R.card * 2 ^ P.card * ∏ p ∈ T', (1 + gm (mS S) p)) := by
    intro S hS
    have hSP := Finset.mem_powerset.1 hS
    have hrS : 0 < rhoS S := rhoS_pos fun p hp => (hP p (hSP hp)).1.two_le
    exact card_Zset_phiT_le hR hSP hP hT hPT n (mS S) (div_pos hθ' hrS)
  have hsumS := Finset.sum_le_sum hS
  have hc1 : (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ) ≤
      Mk.card + ∑ S ∈ P.powerset,
        (((Zset n R P S).filter (fun z => phiT T' z ≤ θ' / rhoS S)).card : ℝ) := by
    have : ((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card ≤ Mk.card + ∑ S ∈ P.powerset,
        ((Zset n R P S).filter (fun z => phiT T' z ≤ θ' / rhoS S)).card := by omega
    exact_mod_cast this
  linarith

/-- **Bad numbers in a residue class**, with the small primes `5 ≤ p ≤ 19`, the middle primes
`23 ≤ p ≤ Y` and the large primes `p > Y`. -/
theorem card_bad_le {R : Finset ℕ} (hR : SymRes R) {θ θ' η : ℝ} (hθ : 0 < θ) (hη0 : 0 < η)
    (hη1 : η < 1) (hθθ' : θ ≤ θ' * (1 - η)) (Y : ℕ) (hY : 23 ≤ Y) (n : ℕ)
    (mS : Finset ℕ → ℕ) :
    (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ) ≤
      n / (η * Y) + ∑ S ∈ P19.powerset, (θ' / rhoS S) ^ mS S *
        ((n : ℝ) / 6 * R.card * dens P19 S * ∏ p ∈ primesIn 23 Y, (1 + gm (mS S) p / p) +
          R.card * 2 ^ P19.card * ∏ p ∈ primesIn 23 Y, (1 + gm (mS S) p)) :=
  card_bad_le_gen hR hθ hη0 hη1 hθθ' P19 (primesIn 23 Y) (primesIn (Y + 1) n) P19_prime
    (primesIn_prime (by norm_num)) (disjoint_P19 Y) Y (by omega)
    (fun p hp => (mem_primesIn.1 hp).1.1) n (fun z hz1 hzn => rho_split hz1 hzn Y (by omega)) mS

/-! ### Rational certificates -/

/-- The exponents available to the certificates. -/
def menu : List ℕ := [0, 3, 6, 10, 15, 20, 25, 30, 40, 50, 60, 70, 85, 99]

/-- Upper bounds for `∏_{p ≥ 23} (1 + g_m(p)/p)`: `Fq 23 m ≤ Fhat m · (1 - 2m/199)`. -/
def Fhat : ℕ → ℚ
  | 0 => 1
  | 3 => 1062769 / 1000000
  | 6 => 566693 / 500000
  | 10 => 1242189 / 1000000
  | 15 => 175977 / 125000
  | 20 => 808521 / 500000
  | 25 => 1886187 / 1000000
  | 30 => 559853 / 250000
  | 40 => 3364983 / 1000000
  | 50 => 225053 / 40000
  | 60 => 10808563 / 1000000
  | 70 => 4980479 / 200000
  | 85 => 146582587 / 1000000
  | 99 => 612932207 / 40000
  | _ => 0

set_option maxRecDepth 100000 in
theorem Fhat_spec : ∀ m ∈ menu, Fq 23 m ≤ Fhat m * (1 - 2 * m / 199) := by
  unfold menu Fq
  decide +kernel

theorem menu_le : ∀ m ∈ menu, 2 * m + 2 ≤ 200 := by decide

/-- The product over the middle primes is at most `Fhat m`. -/
theorem prod_middle_le {m : ℕ} (hm : m ∈ menu) (Y : ℕ) :
    ∏ p ∈ primesIn 23 Y, (1 + gm m p / p) ≤ ((Fhat m : ℚ) : ℝ) := by
  have h1 := prod_primesIn_le 23 m Y (menu_le m hm)
  have h2 : ((Fq 23 m : ℚ) : ℝ) ≤ ((Fhat m * (1 - 2 * m / 199) : ℚ) : ℝ) := by
    exact_mod_cast Fhat_spec m hm
  have hm99 : (m : ℝ) ≤ 99 := by have := menu_le m hm; exact_mod_cast (show m ≤ 99 by omega)
  have hc : (0 : ℝ) < 1 - 2 * m / 199 := by linarith
  push_cast at h2
  have h3 : (∏ p ∈ primesIn 23 Y, (1 + gm m p / p)) * (1 - 2 * m / 199) ≤
      ((Fhat m : ℚ) : ℝ) * (1 - 2 * m / 199) := h1.trans h2
  exact le_of_mul_le_mul_right h3 hc

/-- The best exponent of the menu for the ratio `t`. -/
def bestExp (t : ℚ) : ℕ :=
  menu.foldr (fun m b => if t ^ m * Fhat m < t ^ b * Fhat b then m else b) 0

theorem bestExp_mem (t : ℚ) : bestExp t ∈ menu := by
  have : ∀ L : List ℕ, (∀ m ∈ L, m ∈ menu) →
      L.foldr (fun m b => if t ^ m * Fhat m < t ^ b * Fhat b then m else b) 0 ∈ menu := by
    intro L hL
    induction L with
    | nil => simp [menu]
    | cons a L ih =>
      simp only [List.foldr_cons]
      split_ifs
      · exact hL a List.mem_cons_self
      · exact ih fun m hm => hL m (List.mem_cons_of_mem a hm)
  exact this menu fun m hm => hm

/-- `ρ'(S)` and the density of `S`, as rationals. -/
def rhoSQ (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1 - 1 / (p : ℚ))

def densQ (S : Finset ℕ) : ℚ := (∏ p ∈ P19 \ S, (1 - 1 / (p : ℚ))) / ∏ p ∈ S, (p : ℚ)

theorem rhoSQ_cast (S : Finset ℕ) : ((rhoSQ S : ℚ) : ℝ) = rhoS S := by
  unfold rhoSQ rhoS; push_cast; rfl

theorem densQ_cast (S : Finset ℕ) : ((densQ S : ℚ) : ℝ) = dens P19 S := by
  unfold densQ dens; push_cast; rfl

/-- The certified density for the inflated threshold `θ'`. -/
def certSum (θ' : ℚ) : ℚ :=
  ∑ S ∈ P19.powerset, densQ S * ((θ' / rhoSQ S) ^ bestExp (θ' / rhoSQ S) *
    Fhat (bestExp (θ' / rhoSQ S)))

/-- `#{z ≤ n : z mod 6 ∈ R, ρ'(z) < θ} ≤ (n/6) |R| β` for all large `n`. -/
def BadBound (θ β : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ R : Finset ℕ, SymRes R → R.Nonempty →
    (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ) ≤ n / 6 * R.card * β

/-- The cut between middle and large primes. -/
def Ycut : ℕ := 10 ^ 10

theorem card_le_six {R : Finset ℕ} (hR : SymRes R) : R.card ≤ 6 := by
  have : R ⊆ Finset.range 6 := fun r hr => Finset.mem_range.2 (hR.1 r hr)
  simpa using Finset.card_le_card this

/-- **Certificate theorem.** A rational inequality `certSum θ' + 7/10⁶ ≤ β` with
`θ ≤ θ' (1 - 10⁻⁴)` gives `BadBound θ β`. -/
theorem badBound_of_cert {θ θ' β : ℚ} (hθ : 0 < θ) (hθθ' : θ ≤ θ' * (1 - 1 / 10 ^ 4))
    (hcert : certSum θ' + 7 / 10 ^ 6 ≤ β) : BadBound θ β := by
  set mS : Finset ℕ → ℕ := fun S => bestExp (θ' / rhoSQ S) with hmS
  set t : Finset ℕ → ℝ := fun S => ((θ' : ℝ) / rhoS S) with ht
  set C : Finset ℕ → ℝ := fun S => ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p) with hC
  set C6 : ℝ := ∑ S ∈ P19.powerset, t S ^ mS S * (6 * 2 ^ P19.card * C S) with hC6
  obtain ⟨N, hN⟩ := exists_nat_ge (6 * 10 ^ 6 * C6)
  refine ⟨N, fun n hn R hR hRne => ?_⟩
  have hθr : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hθθ'r : (θ : ℝ) ≤ θ' * (1 - 1 / 10 ^ 4) := by
    have : ((θ : ℚ) : ℝ) ≤ ((θ' * (1 - 1 / 10 ^ 4) : ℚ) : ℝ) := by exact_mod_cast hθθ'
    push_cast at this; exact this
  have hmain := card_bad_le hR hθr (η := 1 / 10 ^ 4) (by norm_num) (by norm_num) hθθ'r Ycut
    (by unfold Ycut; norm_num) n mS
  have hθ'0 : (0 : ℝ) < θ' := by
    have : (0 : ℝ) < θ' * (1 - 1 / 10 ^ 4) := lt_of_lt_of_le hθr hθθ'r
    nlinarith
  have hR1 : (1 : ℝ) ≤ R.card := by exact_mod_cast Finset.card_pos.2 hRne
  have hR6 : (R.card : ℝ) ≤ 6 := by exact_mod_cast card_le_six hR
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrS : ∀ S ∈ P19.powerset, 0 < rhoS S := fun S hS =>
    rhoS_pos fun p hp => (P19_prime p (Finset.mem_powerset.1 hS hp)).1.two_le
  have hC0 : ∀ S, 0 ≤ C S := fun S => Finset.prod_nonneg fun p hp => by
    have := gm_nonneg (mS S) p (mem_primesIn.1 hp).2.two_le; linarith
  -- each signature term
  have hterm : ∀ S ∈ P19.powerset, ((θ' : ℝ) / rhoS S) ^ mS S *
      ((n : ℝ) / 6 * R.card * dens P19 S * ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p / p) +
        R.card * 2 ^ P19.card * ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p)) ≤
      (n : ℝ) / 6 * R.card * ((densQ S * ((θ' / rhoSQ S) ^ mS S * Fhat (mS S)) : ℚ) : ℝ) +
        t S ^ mS S * (6 * 2 ^ P19.card * C S) := by
    intro S hS
    have ht0 : 0 ≤ t S ^ mS S := pow_nonneg (div_pos hθ'0 (hrS S hS)).le _
    have hd0 : 0 ≤ dens P19 S := by rw [← densQ_cast]; exact_mod_cast (show (0 : ℚ) ≤ densQ S by
      unfold densQ
      apply div_nonneg
      · apply Finset.prod_nonneg; intro p hp
        have : (5 : ℚ) ≤ p := by exact_mod_cast (P19_prime p (Finset.mem_sdiff.1 hp).1).2
        have : 1 / (p : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      · apply Finset.prod_nonneg; intro p _; positivity)
    have hF := prod_middle_le (bestExp_mem (θ' / rhoSQ S)) Ycut
    have e1 : ((densQ S * ((θ' / rhoSQ S) ^ mS S * Fhat (mS S)) : ℚ) : ℝ) =
        dens P19 S * (t S ^ mS S * ((Fhat (mS S) : ℚ) : ℝ)) := by
      rw [ht]; push_cast; rw [densQ_cast, rhoSQ_cast]
    rw [e1]
    have h1 : (n : ℝ) / 6 * R.card * dens P19 S * ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p / p) ≤
        (n : ℝ) / 6 * R.card * dens P19 S * ((Fhat (mS S) : ℚ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left hF; positivity
    have h2 : (R.card : ℝ) * 2 ^ P19.card * C S ≤ 6 * 2 ^ P19.card * C S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR6 (by positivity)) (hC0 S)
    calc ((θ' : ℝ) / rhoS S) ^ mS S * ((n : ℝ) / 6 * R.card * dens P19 S *
          ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p / p) +
          R.card * 2 ^ P19.card * ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p))
        = t S ^ mS S * ((n : ℝ) / 6 * R.card * dens P19 S *
          ∏ p ∈ primesIn 23 Ycut, (1 + gm (mS S) p / p)) +
          t S ^ mS S * (R.card * 2 ^ P19.card * C S) := by rw [ht, hC]; ring
      _ ≤ t S ^ mS S * ((n : ℝ) / 6 * R.card * dens P19 S * ((Fhat (mS S) : ℚ) : ℝ)) +
          t S ^ mS S * (6 * 2 ^ P19.card * C S) := by
          gcongr
      _ = (n : ℝ) / 6 * R.card * (dens P19 S * (t S ^ mS S * ((Fhat (mS S) : ℚ) : ℝ))) +
          t S ^ mS S * (6 * 2 ^ P19.card * C S) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hC6] at hsum
  have hcs : ∑ S ∈ P19.powerset, ((densQ S * ((θ' / rhoSQ S) ^ mS S * Fhat (mS S)) : ℚ) : ℝ) =
      ((certSum θ' : ℚ) : ℝ) := by
    unfold certSum; push_cast; rfl
  rw [hcs] at hsum
  have hcert' : ((certSum θ' : ℚ) : ℝ) + 7 / 10 ^ 6 ≤ (β : ℝ) := by
    have : ((certSum θ' + 7 / 10 ^ 6 : ℚ) : ℝ) ≤ ((β : ℚ) : ℝ) := by exact_mod_cast hcert
    push_cast at this; exact this
  have hNn : 6 * 10 ^ 6 * C6 ≤ n := le_trans hN (by exact_mod_cast hn)
  have hY : (n : ℝ) / (1 / 10 ^ 4 * (Ycut : ℝ)) = n / 10 ^ 6 := by
    unfold Ycut; push_cast; field_simp; ring
  rw [hY] at hmain
  set cs : ℝ := ((certSum θ' : ℚ) : ℝ) with hcsdef
  set c := (n : ℝ) / 6 * R.card with hc
  have hc1 : (n : ℝ) / 6 ≤ c := by
    rw [hc]; nlinarith
  have k1 : c * (cs + 7 / 10 ^ 6) ≤ c * β := mul_le_mul_of_nonneg_left hcert' (by positivity)
  have k2 : (n : ℝ) / 6 * (7 / 10 ^ 6) ≤ c * (7 / 10 ^ 6) :=
    mul_le_mul_of_nonneg_right hc1 (by norm_num)
  have k3 : C6 ≤ (n : ℝ) / (6 * 10 ^ 6) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have k4 : c * cs = c * (cs + 7 / 10 ^ 6) - c * (7 / 10 ^ 6) := by ring
  have : c * β = (n : ℝ) / 6 * R.card * β := by rw [hc]
  calc (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ)
      ≤ n / 10 ^ 6 + (c * cs + C6) := by linarith
    _ ≤ (n : ℝ) / 6 * R.card * β := by
        rw [k4]
        have : (n : ℝ) / 10 ^ 6 + (n : ℝ) / (6 * 10 ^ 6) = (n : ℝ) / 6 * (7 / 10 ^ 6) := by ring
        linarith

end ErdosSar
