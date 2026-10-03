import ErdosSar.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Counting elements of `E*(n)` coprime to a given odd number (paper Lemma 2.3)

For a finite set `P` of pairwise coprime numbers, each `≡ ±1 (mod 6)`, let `Cnt n P` be the
number of `w ∈ [1, n]` with `w ≡ 2, 4 (mod 6)` divisible by no element of `P`. Then
`|Cnt n P - (n/3) ∏_{p ∈ P} (1 - 1/p)| ≤ 2^{|P|} - 1/3`.

The proof is by induction on `P`, using `Cnt n (P ∪ {q}) = Cnt n P - Cnt ⌊n/q⌋ P`, instead
of Möbius inversion.
-/

namespace ErdosSar

open Finset

/-- Number of `w ∈ [1, n]`, `w ≡ 2, 4 (mod 6)`, divisible by no element of `P`. -/
def Cnt (n : ℕ) (P : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ P, ¬ p ∣ w)).card

/-- The main term `(n/3) ∏_{p ∈ P} (1 - 1/p)`. -/
noncomputable def mainTerm (n : ℕ) (P : Finset ℕ) : ℝ :=
  (n : ℝ) / 3 * ∏ p ∈ P, (1 - 1 / (p : ℝ))

theorem Cnt_empty (n : ℕ) : Cnt n ∅ = n / 2 - n / 6 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ((Finset.Icc 1 (n + 1)).filter
        (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ w)) =
        if (n + 1) % 6 = 2 ∨ (n + 1) % 6 = 4 then
          insert (n + 1) ((Finset.Icc 1 n).filter
            (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ w))
        else (Finset.Icc 1 n).filter
            (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ w) := by
      split_ifs with hc
      · ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.notMem_empty,
          IsEmpty.forall_iff, implies_true, and_true]
        constructor
        · intro h; omega
        · intro h; omega
      · ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
          IsEmpty.forall_iff, implies_true, and_true]
        constructor
        · intro h; omega
        · intro h; omega
    unfold Cnt at ih ⊢
    rw [h]
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 6 ∧ n = 6 * k + r :=
      ⟨n / 6, n % 6, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 6).symm⟩
    split_ifs with hc
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · rw [ih]
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem Cnt_empty_eq_card_Estar (n : ℕ) : Cnt n ∅ = (Estar n).card := by
  unfold Cnt Estar
  congr 1
  ext w
  simp

/-- Base case of the error estimate. -/
theorem abs_Cnt_empty_sub_le (n : ℕ) : |(Cnt n ∅ : ℝ) - mainTerm n ∅| ≤ 2 / 3 := by
  rw [Cnt_empty, mainTerm, Finset.prod_empty, mul_one]
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 6 ∧ n = 6 * k + r :=
    ⟨n / 6, n % 6, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 6).symm⟩
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (rw [show (6 * k + 0) / 2 - (6 * k + 0) / 6 = 2 * k by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)
    | (rw [show (6 * k + 1) / 2 - (6 * k + 1) / 6 = 2 * k by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)
    | (rw [show (6 * k + 2) / 2 - (6 * k + 2) / 6 = 2 * k + 1 by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)
    | (rw [show (6 * k + 3) / 2 - (6 * k + 3) / 6 = 2 * k + 1 by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)
    | (rw [show (6 * k + 4) / 2 - (6 * k + 4) / 6 = 2 * k + 2 by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)
    | (rw [show (6 * k + 5) / 2 - (6 * k + 5) / 6 = 2 * k + 2 by omega]
       rw [abs_le]; push_cast; constructor <;> linarith)

/-- The recursion `Cnt n (insert q P) = Cnt n P - Cnt (n / q) P`. -/
theorem Cnt_insert {n q : ℕ} {P : Finset ℕ} (hq6 : q % 6 = 1 ∨ q % 6 = 5)
    (hqP : ∀ p ∈ P, Nat.Coprime p q) :
    Cnt n (insert q P) + Cnt (n / q) P = Cnt n P := by
  have hq : 0 < q := by omega
  set S := (Finset.Icc 1 n).filter (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ P, ¬ p ∣ w)
  have hsplit : S.filter (fun w => ¬ q ∣ w) =
      (Finset.Icc 1 n).filter (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ insert q P, ¬ p ∣ w) := by
    ext w
    simp only [S, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
    tauto
  have himage : S.filter (fun w => q ∣ w) =
      ((Finset.Icc 1 (n / q)).filter
        (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ P, ¬ p ∣ w)).image (fun w => q * w) := by
    ext w
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h6, hP⟩, ⟨v, rfl⟩⟩
      refine ⟨v, ⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos v with rfl | hv
        · simp at h1
        · exact hv
      · rw [Nat.le_div_iff_mul_le hq]; linarith [Nat.mul_comm q v]
      · rw [Nat.mul_mod] at h6
        rcases hq6 with h | h <;> rw [h] at h6 <;> omega
      · intro p hp hpv
        exact hP p hp (Dvd.dvd.mul_left hpv q)
    · rintro ⟨v, ⟨⟨h1, h2⟩, h6, hP⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Dvd.intro v rfl⟩
      · exact Nat.mul_pos hq h1
      · rw [Nat.le_div_iff_mul_le hq] at h2; linarith [Nat.mul_comm q v]
      · rw [Nat.mul_mod]
        rcases hq6 with h | h <;> rw [h] <;> omega
      · intro p hp hpv
        exact hP p hp ((hqP p hp).dvd_of_dvd_mul_left hpv)
  have hinj : Set.InjOn (fun w => q * w) (((Finset.Icc 1 (n / q)).filter
      (fun w => (w % 6 = 2 ∨ w % 6 = 4) ∧ ∀ p ∈ P, ¬ p ∣ w)) : Set ℕ) :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq h
  have := Finset.card_filter_add_card_filter_not (s := S) (p := fun w => q ∣ w)
  have e1 : Cnt n (insert q P) = (S.filter (fun w => ¬ q ∣ w)).card := by rw [hsplit]; rfl
  have e2 : Cnt (n / q) P = (S.filter (fun w => q ∣ w)).card := by
    rw [himage, Finset.card_image_of_injOn hinj]; rfl
  have e3 : Cnt n P = S.card := rfl
  rw [e1, e2, e3]
  omega

/-- **Counting lemma.** For `P` pairwise coprime with all elements `≡ ±1 (mod 6)`,
`|Cnt n P - (n/3) ∏ (1 - 1/p)| ≤ 2^{|P|} - 1/3`. -/
theorem abs_Cnt_sub_mainTerm_le (P : Finset ℕ) (hP6 : ∀ p ∈ P, p % 6 = 1 ∨ p % 6 = 5)
    (hPc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Nat.Coprime p q) (n : ℕ) :
    |(Cnt n P : ℝ) - mainTerm n P| ≤ 2 ^ P.card - 1 / 3 := by
  induction P using Finset.induction_on generalizing n with
  | empty =>
    have := abs_Cnt_empty_sub_le n
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
    have hrec := Cnt_insert (n := n) hq6 hcop
    have h1 := ih' n
    have h2 := ih' (n / q)
    -- the main term satisfies the same recursion up to the rounding of `n / q`
    set Pr := ∏ p ∈ P, (1 - 1 / (p : ℝ)) with hPr
    have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun p hp => by
      have : (1 : ℝ) ≤ p := by
        have := hP6 p (Finset.mem_insert_of_mem hp); exact_mod_cast (show 1 ≤ p by omega)
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have hPr1 : Pr ≤ 1 := by
      rw [hPr]
      apply Finset.prod_le_one₀
      · intro p hp
        have : (1 : ℝ) ≤ p := by
          have := hP6 p (Finset.mem_insert_of_mem hp); exact_mod_cast (show 1 ≤ p by omega)
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · intro p hp
        have : (0 : ℝ) < p := by
          have := hP6 p (Finset.mem_insert_of_mem hp); exact_mod_cast (show 0 < p by omega)
        have : 0 < 1 / (p : ℝ) := by positivity
        linarith
    have hmain : mainTerm n (insert q P) =
        mainTerm n P - mainTerm (n / q) P - ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 3 * Pr := by
      simp only [mainTerm, Finset.prod_insert hqP, ← hPr]
      field_simp
      ring
    have hfrac0 : 0 ≤ (n : ℝ) / q - ((n / q : ℕ) : ℝ) := by
      rw [sub_nonneg, le_div_iff₀ hq]
      exact_mod_cast Nat.div_mul_le_self n q
    have hfrac1 : (n : ℝ) / q - ((n / q : ℕ) : ℝ) < 1 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hq]
      have : n < (n / q + 1) * q := by
        have := Nat.lt_succ_iff.2 (le_refl (n / q))
        rw [← Nat.div_lt_iff_lt_mul (by omega)]
        omega
      have h' : (n : ℝ) < (((n / q : ℕ) : ℝ) + 1) * q := by exact_mod_cast this
      linarith
    have hr : 0 ≤ ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 3 * Pr := by positivity
    have hr' : ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 3 * Pr ≤ 1 / 3 := by
      have : ((n : ℝ) / q - ((n / q : ℕ) : ℝ)) / 3 ≤ 1 / 3 := by linarith
      calc _ ≤ 1 / 3 * Pr := by gcongr
        _ ≤ 1 / 3 * 1 := by gcongr
        _ = 1 / 3 := by ring
    have hcast : (Cnt n (insert q P) : ℝ) = Cnt n P - Cnt (n / q) P := by
      rw [← hrec]; push_cast; ring
    rw [hcast, hmain, Finset.card_insert_of_notMem hqP, pow_succ]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end ErdosSar
