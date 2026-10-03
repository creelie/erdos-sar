import ErdosSar.Assembly
import ErdosSar.CoprimePair
import ErdosSar.Moment

/-!
# Triangles

Every `A ⊆ [1, n]` with `|A| > T(n)` and `n ≥ 13` spans a triangle in its coprime graph.

Split the odd numbers into blocks `{6i+1, 6i+3, 6i+5}`; elements of a block are pairwise coprime
and coprime to `6i+2` and `6i+4`. If no triangle exists, a block holds at most two odd elements
of `A`, and when it holds two, both `6i+2` and `6i+4` are missing from `A`. Counting odd
elements against missing even numbers then forces every even number to be in `A`, and a coprime
pair of odd elements together with `2` is a triangle.
-/

namespace ErdosSar

open Finset

theorem hasCycle3 {A : Finset ℕ} {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (cxy : Nat.Coprime x y) (cyz : Nat.Coprime y z) (czx : Nat.Coprime z x) :
    HasCycleOfLength (coprimeGraph A) 3 := by
  have := hasCycle_of_list A x [y, z] (by simp [hxy, hxz, hyz]) (by simp)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)
    (by simp; exact ⟨cxy, cyz, czx⟩)
  simpa using this

theorem coprime_three_of {a : ℕ} (h : ¬ 3 ∣ a) : Nat.Coprime a 3 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm

/-- An odd number in block `i` is coprime to `6i+2` and to `6i+4`. -/
theorem coprime_block_even {w i : ℕ} (hw : w % 2 = 1) (hwi : (w - 1) / 6 = i) :
    Nat.Coprime w (6 * i + 2) ∧ Nat.Coprime w (6 * i + 4) := by
  rcases (by omega : w = 6 * i + 1 ∨ w = 6 * i + 3 ∨ w = 6 * i + 5) with rfl | rfl | rfl
  · constructor
    · rw [show 6 * i + 2 = (6 * i + 1) + 1 by ring]
      exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
    · rw [show 6 * i + 4 = (6 * i + 1) + 3 by ring]
      exact Nat.coprime_self_add_right.2 (coprime_three_of (by omega))
  · constructor
    · rw [show 6 * i + 3 = (6 * i + 2) + 1 by ring]
      exact Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)
    · rw [show 6 * i + 4 = (6 * i + 3) + 1 by ring]
      exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
  · constructor
    · rw [show 6 * i + 5 = (6 * i + 2) + 3 by ring]
      exact Nat.coprime_self_add_left.2 (coprime_three_of (by omega)).symm
    · rw [show 6 * i + 5 = (6 * i + 4) + 1 by ring]
      exact Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)

theorem card_even_Icc (n : ℕ) : ((Finset.Icc 1 n).filter Even).card = n / 2 := by
  rw [← card_filter_dvd_Icc n 2 (by norm_num)]
  congr 1
  apply Finset.filter_congr
  intro z _
  exact even_iff_two_dvd

/-- `|A| > T(n)` forces at least `o(n) + 1 + |D|` odd elements, for any set `D` of even
numbers in `[1, n]` missing from `A`. -/
theorem card_odd_ge {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n) (hcard : T n < A.card)
    (D : Finset ℕ) (hD : D ⊆ (Finset.Icc 1 n).filter Even) (hDA : Disjoint D A) :
    o n + 1 + D.card ≤ (A.filter Odd).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) Odd
  have hsub : A.filter (fun z => ¬ Odd z) ⊆ (Finset.Icc 1 n).filter Even \ D := by
    intro z hz
    obtain ⟨hzA, hz⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hA hzA, Nat.not_odd_iff_even.1 hz⟩, ?_⟩
    exact fun hzD => Finset.disjoint_left.1 hDA hzD hzA
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hD, card_even_Icc] at h1
  have h2 := Finset.card_le_card hD
  rw [card_even_Icc] at h2
  unfold T at hcard
  unfold o
  omega

theorem triangle {n : ℕ} (hn : 13 ≤ n) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hcard : T n < A.card) : HasCycleOfLength (coprimeGraph A) 3 := by
  classical
  by_contra hno
  set O := A.filter Odd with hO
  set Ev := (Finset.Icc 1 n).filter Even with hEv
  set d := (Ev \ A).card with hd
  have hOcard : o n + 1 + d ≤ O.card :=
    card_odd_ge hA hcard (Ev \ A) Finset.sdiff_subset Finset.sdiff_disjoint
  have hOA : ∀ v ∈ O, v ∈ A := fun v hv => (Finset.mem_filter.1 hv).1
  have hOodd : ∀ v ∈ O, v % 2 = 1 := fun v hv => Nat.odd_iff.1 (Finset.mem_filter.1 hv).2
  have hOle : ∀ v ∈ O, 1 ≤ v ∧ v ≤ n := fun v hv => Finset.mem_Icc.1 (hA (hOA v hv))
  -- three odd elements in one block give a triangle
  have h3 : ∀ u ∈ O, ∀ v ∈ O, ∀ w ∈ O, u ≠ v → u ≠ w → v ≠ w →
      (u - 1) / 6 = (v - 1) / 6 → (v - 1) / 6 = (w - 1) / 6 → False := by
    intro u hu v hv w hw huv huw hvw h1 h2
    exact hno (hasCycle3 (hOA u hu) (hOA v hv) (hOA w hw) huv huw hvw
      (coprime_of_same_block (Nat.odd_iff.2 (hOodd u hu)) (Nat.odd_iff.2 (hOodd v hv)) huv h1)
      (coprime_of_same_block (Nat.odd_iff.2 (hOodd v hv)) (Nat.odd_iff.2 (hOodd w hw)) hvw h2)
      (coprime_of_same_block (Nat.odd_iff.2 (hOodd w hw)) (Nat.odd_iff.2 (hOodd u hu))
        (Ne.symm huw) (h1.trans h2).symm))
  -- two odd elements in one block exclude `6i+2` and `6i+4`
  have h2 : ∀ u ∈ O, ∀ v ∈ O, u ≠ v → (u - 1) / 6 = (v - 1) / 6 →
      6 * ((v - 1) / 6) + 2 ∉ A ∧ 6 * ((v - 1) / 6) + 4 ∉ A := by
    intro u hu v hv huv h
    have cu := coprime_block_even (hOodd u hu) h
    have cv := coprime_block_even (hOodd v hv) rfl
    have cuv := coprime_of_same_block (Nat.odd_iff.2 (hOodd u hu)) (Nat.odd_iff.2 (hOodd v hv))
      huv h
    have pu := hOodd u hu
    have pv := hOodd v hv
    constructor
    · intro hw
      exact hno (hasCycle3 (hOA u hu) (hOA v hv) hw huv (by omega) (by omega)
        cuv cv.1 cu.1.symm)
    · intro hw
      exact hno (hasCycle3 (hOA u hu) (hOA v hv) hw huv (by omega) (by omega)
        cuv cv.2 cu.2.symm)
  -- first elements of blocks and the others
  set First := O.filter (fun v => ∀ u ∈ O, (u - 1) / 6 = (v - 1) / 6 → v ≤ u) with hFirst
  set P := O.filter (fun v => ¬ ∀ u ∈ O, (u - 1) / 6 = (v - 1) / 6 → v ≤ u) with hP
  have hsplit : First.card + P.card = O.card :=
    Finset.card_filter_add_card_filter_not _
  have hPmem : ∀ v ∈ P, v ∈ O ∧ ∃ u ∈ O, (u - 1) / 6 = (v - 1) / 6 ∧ u < v := by
    intro v hv
    obtain ⟨hvO, hv⟩ := Finset.mem_filter.1 hv
    push Not at hv
    exact ⟨hvO, hv⟩
  have hFcard : First.card ≤ (n - 1) / 6 + 1 := by
    have hinj : Set.InjOn (fun v => (v - 1) / 6) (First : Set ℕ) := by
      intro v hv v' hv' h
      have hv := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
      have hv' := Finset.mem_filter.1 (Finset.mem_coe.1 hv')
      exact le_antisymm (hv.2 v' hv'.1 h.symm) (hv'.2 v hv.1 h)
    have hmaps : Set.MapsTo (fun v => (v - 1) / 6) (First : Set ℕ)
        (Finset.range ((n - 1) / 6 + 1) : Set ℕ) := by
      intro v hv
      have := (hOle v (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).1).2
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    simpa using Finset.card_le_card_of_injOn _ hmaps hinj
  -- the injection `v ↦ 6i + c` from `P` into the missing even numbers, for `c = 2, 4`
  have hPinj : ∀ c : ℕ, Set.InjOn (fun v => 6 * ((v - 1) / 6) + c) (P : Set ℕ) := by
    intro c v hv v' hv' h
    have h' : (v - 1) / 6 = (v' - 1) / 6 := by simp only at h; omega
    by_contra hne
    obtain ⟨hvO, u, huO, hu, huv⟩ := hPmem v (Finset.mem_coe.1 hv)
    obtain ⟨hv'O, u', hu'O, hu', hu'v'⟩ := hPmem v' (Finset.mem_coe.1 hv')
    by_cases hu_eq : u = v'
    · subst hu_eq
      exact h3 u' hu'O u hv'O v hvO (by omega) (by omega) (by omega) hu' hu
    · exact h3 u huO v hvO v' hv'O (by omega) hu_eq hne hu h'
  have hP2 : ∀ v ∈ P, 6 * ((v - 1) / 6) + 2 ∈ Ev \ A := by
    intro v hv
    obtain ⟨hvO, u, huO, hu, huv⟩ := hPmem v hv
    have hvu := hOle v hvO
    have hpu := hOodd u huO
    have hpv := hOodd v hvO
    have hu1 := (hOle u huO).1
    refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      ⟨3 * ((v - 1) / 6) + 1, by ring⟩⟩, (h2 u huO v hvO (by omega) hu).1⟩
  have hPd : P.card ≤ d := by
    have := Finset.card_le_card_of_injOn _ (fun v hv => Finset.mem_coe.2 (hP2 v hv)) (hPinj 2)
    simpa using this
  have hon : (n - 1) / 6 ≤ o n := by unfold o; omega
  have hn6 : n % 6 = 1 ∨ n % 6 = 2 := by
    have : o n ≤ (n - 1) / 6 := by omega
    unfold o at this; omega
  have hdP : d ≤ P.card := by omega
  have hP4 : ∀ v ∈ P, 6 * ((v - 1) / 6) + 4 ∈ Ev \ A := by
    intro v hv
    obtain ⟨hvO, u, huO, hu, huv⟩ := hPmem v hv
    have hvu := hOle v hvO
    have hpu := hOodd u huO
    have hpv := hOodd v hvO
    have hu1 := (hOle u huO).1
    refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      ⟨3 * ((v - 1) / 6) + 2, by ring⟩⟩, (h2 u huO v hvO (by omega) hu).2⟩
  have hdisj : Disjoint (P.image fun v => 6 * ((v - 1) / 6) + 2)
      (P.image fun v => 6 * ((v - 1) / 6) + 4) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v', -, h⟩ := Finset.mem_image.1 hx'
    omega
  have hunion : (P.image fun v => 6 * ((v - 1) / 6) + 2) ∪
      (P.image fun v => 6 * ((v - 1) / 6) + 4) ⊆ Ev \ A := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx; exact hP2 v hv
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx; exact hP4 v hv
  have h2P : 2 * P.card ≤ d := by
    have := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn (hPinj 2),
      Finset.card_image_of_injOn (hPinj 4)] at this
    omega
  have hd0 : d = 0 := by omega
  have h2A : 2 ∈ A := by
    by_contra h2A
    have : 2 ∈ Ev \ A := Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2
      ⟨by norm_num, by omega⟩, even_two⟩, h2A⟩
    have := Finset.card_pos.2 ⟨2, this⟩
    omega
  obtain ⟨a, ha, b, hb, hab, hcop⟩ := coprime_pair hn O
    (fun v hv => hA (hOA v hv)) (fun v hv => Nat.odd_iff.2 (hOodd v hv)) (by omega)
  have pa := hOodd a ha
  have pb := hOodd b hb
  exact hno (hasCycle3 (hOA a ha) (hOA b hb) h2A hab (by omega) (by omega) hcop
    (Nat.coprime_two_right.2 (Nat.odd_iff.2 pb)) (Nat.coprime_two_left.2 (Nat.odd_iff.2 pa)))

end ErdosSar
