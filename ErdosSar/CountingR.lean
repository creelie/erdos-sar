import ErdosSar.Rho

/-!
# Counting elements of a residue class mod 6 coprime to a given number

`Counting.lean` treats the class `E* = {w ≡ 2, 4 (mod 6)}`. Here the same estimate is proved for
any set `R` of residues mod 6 that is closed under `r ↦ -r`, which covers the multiples of `6`,
the odd multiples of `3`, the units `w ≡ ±1 (mod 6)`, all even numbers and all multiples of `2`
or `3`. For such `R` and a set `P` of pairwise coprime numbers `≡ ±1 (mod 6)`,
`|#{w ≤ n : w mod 6 ∈ R, p ∤ w for p ∈ P} - (n/6) |R| ∏_{p ∈ P} (1 - 1/p)| ≤ |R| (2^{|P|} - 1/6)`.
-/

namespace ErdosSar

open Finset

/-- Number of `w ∈ [1, n]` with `w mod 6 ∈ R` divisible by no element of `P`. -/
def CntR (n : ℕ) (R P : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun w => w % 6 ∈ R ∧ ∀ p ∈ P, ¬ p ∣ w)).card

/-- The main term `(n/6) |R| ∏_{p ∈ P} (1 - 1/p)`. -/
noncomputable def mainTermR (n : ℕ) (R P : Finset ℕ) : ℝ :=
  (n : ℝ) / 6 * R.card * ∏ p ∈ P, (1 - 1 / (p : ℝ))

/-- A set of residues mod 6 closed under negation. -/
def SymRes (R : Finset ℕ) : Prop := (∀ r ∈ R, r < 6) ∧ ∀ r ∈ R, (6 - r) % 6 ∈ R

/-- The number of `w ∈ [1, n]` with `w ≡ r (mod 6)`, where `r = r' mod 6`, `1 ≤ r' ≤ 6`. -/
theorem card_res (n r r' : ℕ) (h1 : 1 ≤ r') (h6 : r' ≤ 6) (hrr : r' % 6 = r) :
    ((Finset.Icc 1 n).filter (fun w => w % 6 = r)).card = (n + 6 - r') / 6 := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    have h : (Finset.Icc 1 (n + 1)).filter (fun w => w % 6 = r) =
        if (n + 1) % 6 = r then insert (n + 1) ((Finset.Icc 1 n).filter (fun w => w % 6 = r))
        else (Finset.Icc 1 n).filter (fun w => w % 6 = r) := by
      split_ifs with hc
      · ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
        constructor
        · intro h; omega
        · intro h; omega
      · ext x
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro h; omega
        · intro h; omega
    rw [h]
    split_ifs with hc
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

theorem abs_card_res_sub_le (n r : ℕ) (hr : r < 6) :
    |(((Finset.Icc 1 n).filter (fun w => w % 6 = r)).card : ℝ) - (n : ℝ) / 6| ≤ 5 / 6 := by
  obtain ⟨r', h1, h6, hrr⟩ : ∃ r', 1 ≤ r' ∧ r' ≤ 6 ∧ r' % 6 = r :=
    ⟨if r = 0 then 6 else r, by split_ifs <;> omega, by split_ifs <;> omega,
      by split_ifs <;> omega⟩
  rw [card_res n r r' h1 h6 hrr]
  have hlo : 6 * ((n + 6 - r') / 6) + 5 ≥ n + 6 - r' := by omega
  have hhi : 6 * ((n + 6 - r') / 6) ≤ n + 6 - r' := Nat.mul_div_le _ _
  have hsub : ((n + 6 - r' : ℕ) : ℝ) = n + 6 - r' := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlo' : (6 : ℝ) * ((n + 6 - r') / 6 : ℕ) + 5 ≥ n + 6 - r' := by
    rw [← hsub]; exact_mod_cast hlo
  have hhi' : (6 : ℝ) * ((n + 6 - r') / 6 : ℕ) ≤ n + 6 - r' := by
    rw [← hsub]; exact_mod_cast hhi
  have h1' : (1 : ℝ) ≤ r' := by exact_mod_cast h1
  have h6' : (r' : ℝ) ≤ 6 := by exact_mod_cast h6
  rw [abs_le]; constructor <;> linarith

theorem CntR_empty (n : ℕ) (R : Finset ℕ) :
    CntR n R ∅ = ∑ r ∈ R, ((Finset.Icc 1 n).filter (fun w => w % 6 = r)).card := by
  unfold CntR
  rw [← Finset.card_biUnion]
  · congr 1
    ext w
    simp [and_comm]
  · intro r _ s _ hrs
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    exact hrs ((Finset.mem_filter.1 hw).2.symm.trans (Finset.mem_filter.1 hw').2)

theorem abs_CntR_empty_sub_le (n : ℕ) {R : Finset ℕ} (hR : SymRes R) :
    |(CntR n R ∅ : ℝ) - mainTermR n R ∅| ≤ R.card * (5 / 6) := by
  rw [CntR_empty, mainTermR, Finset.prod_empty, mul_one]
  push_cast
  have : (n : ℝ) / 6 * R.card = ∑ r ∈ R, (n : ℝ) / 6 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [this, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ r ∈ R, |(((Finset.Icc 1 n).filter (fun w => w % 6 = r)).card : ℝ) - (n : ℝ) / 6| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ R, (5 / 6 : ℝ) := Finset.sum_le_sum fun r hr => abs_card_res_sub_le n r (hR.1 r hr)
    _ = R.card * (5 / 6) := by rw [Finset.sum_const, nsmul_eq_mul]

theorem mul_mod_mem_iff {R : Finset ℕ} (hR : SymRes R) {q : ℕ} (hq6 : q % 6 = 1 ∨ q % 6 = 5)
    (v : ℕ) : (q * v) % 6 ∈ R ↔ v % 6 ∈ R := by
  rcases hq6 with h | h
  · rw [show (q * v) % 6 = v % 6 by rw [Nat.mul_mod, h]; omega]
  · rw [show (q * v) % 6 = (6 - v % 6) % 6 by rw [Nat.mul_mod, h]; omega]
    constructor
    · intro hm
      have := hR.2 _ hm
      rwa [show (6 - (6 - v % 6) % 6) % 6 = v % 6 by omega] at this
    · exact hR.2 _

/-- The recursion `CntR n R (insert q P) = CntR n R P - CntR (n / q) R P`. -/
theorem CntR_insert {n q : ℕ} {R P : Finset ℕ} (hR : SymRes R) (hq6 : q % 6 = 1 ∨ q % 6 = 5)
    (hqP : ∀ p ∈ P, Nat.Coprime p q) :
    CntR n R (insert q P) + CntR (n / q) R P = CntR n R P := by
  have hq : 0 < q := by omega
  set S := (Finset.Icc 1 n).filter (fun w => w % 6 ∈ R ∧ ∀ p ∈ P, ¬ p ∣ w)
  have hsplit : S.filter (fun w => ¬ q ∣ w) =
      (Finset.Icc 1 n).filter (fun w => w % 6 ∈ R ∧ ∀ p ∈ insert q P, ¬ p ∣ w) := by
    ext w
    simp only [S, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
    tauto
  have himage : S.filter (fun w => q ∣ w) =
      ((Finset.Icc 1 (n / q)).filter
        (fun w => w % 6 ∈ R ∧ ∀ p ∈ P, ¬ p ∣ w)).image (fun w => q * w) := by
    ext w
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h6, hP⟩, ⟨v, rfl⟩⟩
      refine ⟨v, ⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos v with rfl | hv
        · simp at h1
        · exact hv
      · rw [Nat.le_div_iff_mul_le hq]; linarith [Nat.mul_comm q v]
      · exact (mul_mod_mem_iff hR hq6 v).1 h6
      · intro p hp hpv
        exact hP p hp (Dvd.dvd.mul_left hpv q)
    · rintro ⟨v, ⟨⟨h1, h2⟩, h6, hP⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Dvd.intro v rfl⟩
      · exact Nat.mul_pos hq h1
      · rw [Nat.le_div_iff_mul_le hq] at h2; linarith [Nat.mul_comm q v]
      · exact (mul_mod_mem_iff hR hq6 v).2 h6
      · intro p hp hpv
        exact hP p hp ((hqP p hp).dvd_of_dvd_mul_left hpv)
  have hinj : Set.InjOn (fun w => q * w) (((Finset.Icc 1 (n / q)).filter
      (fun w => w % 6 ∈ R ∧ ∀ p ∈ P, ¬ p ∣ w)) : Set ℕ) :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq h
  have := Finset.card_filter_add_card_filter_not (s := S) (p := fun w => q ∣ w)
  have e1 : CntR n R (insert q P) = (S.filter (fun w => ¬ q ∣ w)).card := by rw [hsplit]; rfl
  have e2 : CntR (n / q) R P = (S.filter (fun w => q ∣ w)).card := by
    rw [himage, Finset.card_image_of_injOn hinj]; rfl
  have e3 : CntR n R P = S.card := rfl
  rw [e1, e2, e3]
  omega

/-- **Counting lemma for residue classes.** -/
theorem abs_CntR_sub_mainTermR_le {R : Finset ℕ} (hR : SymRes R) (P : Finset ℕ)
    (hP6 : ∀ p ∈ P, p % 6 = 1 ∨ p % 6 = 5)
    (hPc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Nat.Coprime p q) (n : ℕ) :
    |(CntR n R P : ℝ) - mainTermR n R P| ≤ R.card * (2 ^ P.card - 1 / 6) := by
  induction P using Finset.induction_on generalizing n with
  | empty =>
    have := abs_CntR_empty_sub_le n hR
    simp only [Finset.card_empty, pow_zero]
    linarith
  | @insert q P hqP ih =>
    have hq6 : q % 6 = 1 ∨ q % 6 = 5 := hP6 q (Finset.mem_insert_self q P)
    have hq : (0 : ℝ) < q := by
      have : 0 < q := by omega
      exact_mod_cast this
    have ih' := ih (fun p hp => hP6 p (Finset.mem_insert_of_mem hp))
      (fun p hp p' hp' h => hPc p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp') h)
    have hcop : ∀ p ∈ P, Nat.Coprime p q := fun p hp =>
      hPc p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_self q P)
        (fun h => hqP (h ▸ hp))
    have hrec := CntR_insert (n := n) hR hq6 hcop
    have h1 := ih' n
    have h2 := ih' (n / q)
    set Pr := ∏ p ∈ P, (1 - 1 / (p : ℝ)) with hPr
    have hp1 : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
      have := hP6 p (Finset.mem_insert_of_mem hp); exact_mod_cast (show 1 ≤ p by omega)
    have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun p hp => by
      have := hp1 p hp
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have hPr1 : Pr ≤ 1 := by
      rw [hPr]
      apply Finset.prod_le_one₀
      · intro p hp
        have := hp1 p hp
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · intro p hp
        have : (0 : ℝ) < p := by linarith [hp1 p hp]
        have : 0 < 1 / (p : ℝ) := by positivity
        linarith
    set c : ℝ := (R.card : ℝ) with hc
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    have hmain : mainTermR n R (insert q P) =
        mainTermR n R P - mainTermR (n / q) R P -
          ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 6 * c * Pr := by
      simp only [mainTermR, Finset.prod_insert hqP, ← hPr, ← hc]
      field_simp
      ring
    have hfrac0 : 0 ≤ (n : ℝ) / q - ((n / q : ℕ) : ℝ) := by
      rw [sub_nonneg, le_div_iff₀ hq]
      exact_mod_cast Nat.div_mul_le_self n q
    have hfrac1 : (n : ℝ) / q - ((n / q : ℕ) : ℝ) < 1 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hq]
      have : n < (n / q + 1) * q := by
        rw [← Nat.div_lt_iff_lt_mul (by omega)]
        omega
      have h' : (n : ℝ) < (((n / q : ℕ) : ℝ) + 1) * q := by exact_mod_cast this
      linarith
    have hr : 0 ≤ ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 6 * c * Pr := by positivity
    have hr' : ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 6 * c * Pr ≤ c / 6 := by
      have : ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 6 ≤ 1 / 6 := by linarith
      calc _ ≤ 1 / 6 * c * Pr := by gcongr
        _ ≤ 1 / 6 * c * 1 := by gcongr
        _ = c / 6 := by ring
    have hcast : (CntR n R (insert q P) : ℝ) = CntR n R P - CntR (n / q) R P := by
      rw [← hrec]; push_cast; ring
    rw [hcast, hmain, Finset.card_insert_of_notMem hqP, pow_succ]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The elements of a residue class coprime to `m`, when the primes `2, 3` of `m` cannot divide
elements of the class. -/
theorem card_class_coprime {n m : ℕ} {R : Finset ℕ} (hm0 : m ≠ 0)
    (h2 : 2 ∣ m → ∀ r ∈ R, r % 2 = 1) (h3 : 3 ∣ m → ∀ r ∈ R, r % 3 ≠ 0) :
    ((Finset.Icc 1 n).filter (fun w => w % 6 ∈ R ∧ Nat.Coprime w m)).card =
      CntR n R (bigPrimes m) := by
  unfold CntR
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
    rcases (by have := hpr.two_le; omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · subst h
      have := h2 hpm _ h6
      omega
    · subst h
      have := h3 hpm _ h6
      omega
    · subst h; exact absurd hpr (by decide)
    · exact hP p (mem_bigPrimes.2 ⟨hpr, hpm, hm0, h⟩) hpw

/-- The number of elements of a symmetric residue class coprime to `m` is
`(n/6) |R| ρ'(m)` up to `|R| 2^{ω'(m)}`. -/
theorem abs_card_class_coprime_sub_le {n m : ℕ} {R : Finset ℕ} (hR : SymRes R) (hm0 : m ≠ 0)
    (h2 : 2 ∣ m → ∀ r ∈ R, r % 2 = 1) (h3 : 3 ∣ m → ∀ r ∈ R, r % 3 ≠ 0) :
    |(((Finset.Icc 1 n).filter (fun w => w % 6 ∈ R ∧ Nat.Coprime w m)).card : ℝ) -
        (n : ℝ) / 6 * R.card * rho m| ≤ R.card * (2 ^ (bigPrimes m).card - 1 / 6) := by
  rw [card_class_coprime hm0 h2 h3]
  exact abs_CntR_sub_mainTermR_le hR _ (fun p hp => bigPrimes_mod_six hp)
    (fun p hp q hq h => bigPrimes_coprime hp hq h) n

end ErdosSar
