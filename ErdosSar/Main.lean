import ErdosSar.LongCycle
import ErdosSar.Short
import ErdosSar.Triangle
import ErdosSar.CoprimePair

/-!
# The main theorem (paper Theorem 1.1)

For `n ≥ N₀`, every `A ⊆ [1, n]` with `|A| > T(n)` that omits at most `n/70` elements of `E*(n)`
contains a cycle of length `2l + 1` in its coprime graph for every `1 ≤ l ≤ o(n)`.
-/

namespace ErdosSar

open Finset

/-- Choice of the odd vertices: `l - 1` elements of `O''`, enough of them easy to give every hard
element two partners. -/
theorem exists_X1 (O'' : Finset ℕ) (l : ℕ) (hl4 : 4 ≤ l) (hlO : l - 1 ≤ O''.card)
    (hEy : 2 * (O''.filter (fun z => rho z < 14 / 25)).card + 2 ≤
      (O''.filter (fun z => 3 / 4 ≤ rho z)).card) :
    ∃ X1 ⊆ O'', X1.card = l - 1 ∧
      2 * (X1.filter (fun z => rho z < 14 / 25)).card + 2 ≤
        (X1.filter (fun z => 3 / 4 ≤ rho z)).card ∧
      4 + 2 * (X1.filter (fun z => rho z < 14 / 25)).card ≤ l ∧
      (X1.filter (fun z => rho z < 14 / 25)).card ≤ (O''.filter (fun z => rho z < 14 / 25)).card := by
  classical
  set Hd := O''.filter (fun z => rho z < 14 / 25) with hHd
  set Ey := O''.filter (fun z => 3 / 4 ≤ rho z) with hEy'
  set N1 := O''.filter (fun z => ¬ rho z < 14 / 25) with hN1
  have hEyN : Ey ⊆ N1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨h1, by push Not; linarith⟩
  have hsplit : Hd.card + N1.card = O''.card := Finset.card_filter_add_card_filter_not _
  rcases le_or_gt (l - 1) N1.card with hcase | hcase
  · obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (show 2 ≤ Ey.card by omega)
    obtain ⟨X1, hQX, hXN, hXc⟩ := Finset.exists_subsuperset_card_eq (hQ.trans hEyN)
      (show Q.card ≤ l - 1 by omega) hcase
    have hhard : X1.filter (fun z => rho z < 14 / 25) = ∅ := by
      apply Finset.filter_false_of_mem
      intro z hz
      exact (Finset.mem_filter.1 (hXN hz)).2
    have heasy : 2 ≤ (X1.filter (fun z => 3 / 4 ≤ rho z)).card := by
      have : Q.card ≤ (X1.filter (fun z => 3 / 4 ≤ rho z)).card := by
        apply Finset.card_le_card
        intro z hz
        exact Finset.mem_filter.2 ⟨hQX hz, (Finset.mem_filter.1 (hQ hz)).2⟩
      omega
    refine ⟨X1, hXN.trans (Finset.filter_subset _ _), hXc, ?_, ?_, ?_⟩
    · rw [hhard]; simpa using heasy
    · rw [hhard]; simpa using hl4
    · rw [hhard]; simp
  · obtain ⟨H', hH', hH'c⟩ := Finset.exists_subset_card_eq
      (show l - 1 - N1.card ≤ Hd.card by omega)
    have hdisj : Disjoint N1 H' := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      exact (Finset.mem_filter.1 hz).2 (Finset.mem_filter.1 (hH' hz')).2
    set X1 := N1 ∪ H' with hX1
    have hhard : X1.filter (fun z => rho z < 14 / 25) = H' := by
      ext z
      simp only [Finset.mem_filter, hX1, Finset.mem_union]
      constructor
      · rintro ⟨hz | hz, hr⟩
        · exact absurd hr (Finset.mem_filter.1 hz).2
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, (Finset.mem_filter.1 (hH' hz)).2⟩
    have heasy : X1.filter (fun z => 3 / 4 ≤ rho z) = Ey := by
      ext z
      simp only [Finset.mem_filter, hX1, Finset.mem_union]
      constructor
      · rintro ⟨hz | hz, hr⟩
        · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, hr⟩
        · have := (Finset.mem_filter.1 (hH' hz)).2
          linarith
      · intro hz
        exact ⟨Or.inl (hEyN hz), (Finset.mem_filter.1 hz).2⟩
    have hX1c : X1.card = l - 1 := by
      rw [hX1, Finset.card_union_of_disjoint hdisj, hH'c]; omega
    have hHH : H'.card ≤ Hd.card := Finset.card_le_card hH'
    have hEyc : Ey.card ≤ N1.card := Finset.card_le_card hEyN
    refine ⟨X1, Finset.union_subset (Finset.filter_subset _ _) (hH'.trans
      (Finset.filter_subset _ _)), hX1c, ?_, ?_, ?_⟩
    · rw [hhard, heasy]; omega
    · rw [hhard]; omega
    · rw [hhard]; exact hHH

/-- **Paper Theorem 1.1**, formally verified. -/
theorem paperTheorem_holds : PaperTheorem := by
  refine ⟨N₀, fun n hn A hA hcard hD l hl1 hlo => ?_⟩
  classical
  have hn13 : 13 ≤ n := le_trans (by unfold N₀; norm_num) hn
  have hnbig : (100000 : ℝ) ≤ n := by
    have : (100000 : ℕ) ≤ n := le_trans (by unfold N₀; norm_num) hn
    exact_mod_cast this
  rcases (by omega : l = 1 ∨ 2 ≤ l) with rfl | hl2
  · exact triangle hn13 A hA hcard
  set D := Estar n \ A with hDdef
  set O := A.filter Odd with hOdef
  have hDev : D ⊆ (Icc 1 n).filter Even := by
    intro w hw
    obtain ⟨hwE, -⟩ := Finset.mem_sdiff.1 hw
    obtain ⟨hwI, hw6⟩ := mem_Estar.1 hwE
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hwI, Nat.even_iff.2 (by omega)⟩
  have hO : o n + 1 + D.card ≤ O.card := card_odd_ge hA hcard D hDev Finset.sdiff_disjoint
  have hOI : O ⊆ Icc 1 n := fun z hz => hA (Finset.mem_filter.1 hz).1
  set O' := O.filter (Undamaged n A) with hO'def
  have hO' : o n + 1 ≤ O'.card := by
    have h1 : (O.filter (fun z => ¬ Undamaged n A z)).card ≤ D.card := card_damaged_le hOI hD
    have h2 : O'.card + (O.filter (fun z => ¬ Undamaged n A z)).card = O.card :=
      Finset.card_filter_add_card_filter_not _
    omega
  have hO'mem : ∀ z ∈ O', z ∈ A ∧ z % 2 = 1 ∧ Undamaged n A z ∧ z ∈ Icc 1 n := by
    intro z hz
    obtain ⟨hzO, hzU⟩ := Finset.mem_filter.1 hz
    obtain ⟨hzA, hzodd⟩ := Finset.mem_filter.1 hzO
    exact ⟨hzA, Nat.odd_iff.1 hzodd, hzU, hA hzA⟩
  obtain ⟨a, ha, b, hb, hab, hcop⟩ := coprime_pair hn13 O'
    (fun z hz => (hO'mem z hz).2.2.2) (fun z hz => Nat.odd_iff.2 (hO'mem z hz).2.1) hO'
  obtain ⟨haA, ha2, haU, haI⟩ := hO'mem a ha
  obtain ⟨hbA, hb2, hbU, hbI⟩ := hO'mem b hb
  set O'' := O' \ {a, b} with hO''def
  have hO''mem : ∀ z ∈ O'', (z ∈ A ∧ z % 2 = 1 ∧ Undamaged n A z ∧ z ∈ Icc 1 n) ∧
      z ≠ a ∧ z ≠ b := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz2
    exact ⟨hO'mem z hz1, hz2⟩
  have hO''c : o n - 1 ≤ O''.card := by
    have h1 : O'.card - ({a, b} : Finset ℕ).card ≤ O''.card := Finset.le_card_sdiff _ _
    have h2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair_eq_two_iff.2 hab
    omega
  set Hd := O''.filter (fun z => rho z < 14 / 25) with hHd
  set Ey := O''.filter (fun z => 3 / 4 ≤ rho z) with hEy
  have hHd_le : (Hd.card : ℝ) ≤ n / 1000 := by
    have hsub : Hd ⊆ (Icc 1 n).filter (fun z => rho z ≤ 14 / 25) := by
      intro z hz
      obtain ⟨hzO, hzr⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_filter.2 ⟨(hO''mem z hzO).1.2.2.2, hzr.le⟩
    have h1 := card_rho_le n (x := 14 / 25) (by norm_num) le_rfl
    have h2 : (Hd.card : ℝ) ≤ ((Icc 1 n).filter (fun z => rho z ≤ 14 / 25)).card := by
      exact_mod_cast Finset.card_le_card hsub
    linarith
  have hEy_ge : 2 * Hd.card + 2 ≤ Ey.card := by
    have hsub : O'' \ Ey ⊆ (Icc 1 n).filter (fun z => z % 2 = 1 ∧ rho z < 3 / 4) := by
      intro z hz
      obtain ⟨hzO, hzE⟩ := Finset.mem_sdiff.1 hz
      have hm := hO''mem z hzO
      refine Finset.mem_filter.2 ⟨hm.1.2.2.2, hm.1.2.1, ?_⟩
      by_contra h
      push Not at h
      exact hzE (Finset.mem_filter.2 ⟨hzO, h⟩)
    have h1 := card_nonEasy_le n
    have h2 : (((O'' \ Ey).card : ℕ) : ℝ) ≤
        ((Icc 1 n).filter (fun z => z % 2 = 1 ∧ rho z < 3 / 4)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have h3 := Finset.card_le_card_sdiff_add_card (s := O'') (t := Ey)
    have h4 : n ≤ 6 * o n + 6 := by unfold o; omega
    have h5 : (n : ℝ) ≤ 6 * (o n : ℝ) + 6 := by exact_mod_cast h4
    have h6 : (((n / 70 + 1 : ℕ)) : ℝ) ≤ (n : ℝ) / 70 + 1 := by
      push_cast
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := 70)
      push_cast at this
      linarith
    have h7 : ((o n - 1 : ℕ) : ℝ) ≥ (o n : ℝ) - 1 := by
      rcases Nat.eq_zero_or_pos (o n) with h | h
      · rw [h]; simp
      · rw [Nat.cast_sub h]; simp
    have h8 : ((o n - 1 : ℕ) : ℝ) ≤ O''.card := by exact_mod_cast hO''c
    have h3' : (O''.card : ℝ) ≤ (O'' \ Ey).card + Ey.card := by exact_mod_cast h3
    have : (2 * Hd.card + 2 : ℝ) ≤ Ey.card := by linarith
    exact_mod_cast this
  have hEy2 : 2 ≤ Ey.card := by omega
  have hEymem : ∀ y ∈ Ey, ((y ∈ A ∧ y % 2 = 1 ∧ Undamaged n A y ∧ y ∈ Icc 1 n) ∧
      y ≠ a ∧ y ≠ b) ∧ 3 / 4 ≤ rho y := by
    intro y hy
    obtain ⟨hyO, hyr⟩ := Finset.mem_filter.1 hy
    exact ⟨hO''mem y hyO, hyr⟩
  rcases (by omega : l = 2 ∨ l = 3 ∨ 4 ≤ l) with rfl | rfl | hl4
  · obtain ⟨y, hy⟩ := Finset.card_pos.1 (show 0 < Ey.card by omega)
    obtain ⟨⟨⟨hyA, hy2, -, -⟩, hya, hyb⟩, hyE⟩ := hEymem y hy
    exact cycle_five hn hA haA hbA hyA ha2 hb2 hy2 hab hya hyb hcop haU hbU hyE
  · obtain ⟨ya, hya, yb, hyb, hne⟩ := Finset.one_lt_card.1 (show 1 < Ey.card by omega)
    obtain ⟨⟨⟨hyaA, hya2, -, -⟩, hya1, hya3⟩, hyaE⟩ := hEymem ya hya
    obtain ⟨⟨⟨hybA, hyb2, hybU, -⟩, hyb1, hyb3⟩, hybE⟩ := hEymem yb hyb
    exact cycle_seven hn hA haA hbA hyaA hybA ha2 hb2 hya2 hyb2 hab hya1 hya3 hyb1 hyb3 hne
      hcop haU hbU hybU hyaE hybE
  · obtain ⟨X1, hX1, hX1c, hpart, hl, hHH⟩ := exists_X1 O'' l hl4 (by omega) hEy_ge
    refine long_cycle hn hA hD haA hbA ha2 hb2 hab hcop haU hbU X1
      (fun z hz => (hO''mem z (hX1 hz)).1.1) (fun z hz => (hO''mem z (hX1 hz)).1.2.1)
      (fun z hz => (hO''mem z (hX1 hz)).1.2.2.1)
      (fun h => (hO''mem a (hX1 h)).2.1 rfl) (fun h => (hO''mem b (hX1 h)).2.2 rfl)
      l hX1c hlo hpart hl ?_
    have : ((X1.filter (fun z => rho z < 14 / 25)).card : ℝ) ≤ Hd.card := by
      exact_mod_cast hHH
    linarith

/-- In particular Question 1 holds for all sets omitting at most `n/70` elements of `E*(n)`. -/
theorem question1_restricted : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
    T n < A.card → 70 * (Estar n \ A).card ≤ n →
    ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ n / 3 + 1 → HasCycleOfLength (coprimeGraph A) L := by
  obtain ⟨n₀, h⟩ := paperTheorem_holds
  refine ⟨max n₀ 13, fun n hn A hA hcard hD L hL h3 hLn => ?_⟩
  obtain ⟨l, rfl⟩ := hL
  apply h n (le_trans (le_max_left _ _) hn) A hA hcard hD l (by omega)
  have : 13 ≤ n := le_trans (le_max_right _ _) hn
  unfold o; omega

end ErdosSar
