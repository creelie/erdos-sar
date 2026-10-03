import ErdosSar.Setup
import ErdosSar.Assembly
import ErdosSar.Greedy

/-!
# Long cycles (paper Section 4)

Given the coprime pair `a, b`, a set `X₁` of `l - 1` further odd vertices whose hard elements
can each be given two easy partners, we build the closing path
`y_a, w_a, a, b, w_b, y_b`, one path `y, w, z, w', y'` through every hard `z`, and close
everything up with Jackson's theorem applied to the remaining elements of `E* ∩ A`.
-/

namespace ErdosSar

open Finset

theorem nodup_closing {p0 w0 a b w1 p1 : ℕ} (hp0 : p0 % 2 = 1) (ha : a % 2 = 1)
    (hb : b % 2 = 1) (hp1 : p1 % 2 = 1) (hw0 : w0 % 2 = 0) (hw1 : w1 % 2 = 0)
    (h1 : p0 ≠ p1) (h2 : w0 ≠ w1) (h3 : a ≠ b) (h4 : a ≠ p0) (h5 : a ≠ p1) (h6 : b ≠ p0)
    (h7 : b ≠ p1) : [p0, w0, a, b, w1, p1].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
    not_or, not_false_eq_true, and_true]
  omega

theorem nodup_gadget {p0 w0 z w1 p1 : ℕ} (hp0 : p0 % 2 = 1) (hz : z % 2 = 1)
    (hp1 : p1 % 2 = 1) (hw0 : w0 % 2 = 0) (hw1 : w1 % 2 = 0)
    (h1 : p0 ≠ p1) (h2 : w0 ≠ w1) (h4 : z ≠ p0) (h5 : z ≠ p1) :
    [p0, w0, z, w1, p1].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
    not_or, not_false_eq_true, and_true]
  omega

theorem chain_closing {n p0 w0 a b w1 p1 : ℕ} (hw0 : w0 ∈ Nstar n (Nat.lcm p0 a))
    (hw1 : w1 ∈ Nstar n (Nat.lcm p1 b)) (hab : Nat.Coprime a b) :
    [p0, w0, a, b, w1, p1].IsChain Nat.Coprime := by
  have c0 := coprime_of_mem_Nstar_lcm hw0
  have c1 := coprime_of_mem_Nstar_lcm hw1
  simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
  exact ⟨c0.1.symm, c0.2, hab, c1.2.symm, c1.1⟩

theorem chain_gadget {n p0 w0 z w1 p1 : ℕ} (hw0 : w0 ∈ Nstar n (Nat.lcm p0 z))
    (hw1 : w1 ∈ Nstar n (Nat.lcm p1 z)) :
    [p0, w0, z, w1, p1].IsChain Nat.Coprime := by
  have c0 := coprime_of_mem_Nstar_lcm hw0
  have c1 := coprime_of_mem_Nstar_lcm hw1
  simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
  exact ⟨c0.1.symm, c0.2, c1.2.symm, c1.1⟩

/-- The paths: the closing path for `a`, a five-vertex path for each hard `c ∈ H`, and the
one-vertex path `[c]` otherwise. -/
def exList (a b : ℕ) (H : Finset ℕ) (π ω : ℕ × ℕ → ℕ) (c : ℕ) : List ℕ :=
  if c = a then [π (a, 0), ω (a, 0), a, b, ω (b, 1), π (b, 1)]
  else if c ∈ H then [π (c, 0), ω (c, 0), c, ω (c, 1), π (c, 1)] else [c]

theorem exList_a (a b : ℕ) (H : Finset ℕ) (π ω : ℕ × ℕ → ℕ) :
    exList a b H π ω a = [π (a, 0), ω (a, 0), a, b, ω (b, 1), π (b, 1)] := by
  simp [exList]

theorem exList_H {a b : ℕ} {H : Finset ℕ} (π ω : ℕ × ℕ → ℕ) {c : ℕ} (hc : c ∈ H) (hca : c ≠ a) :
    exList a b H π ω c = [π (c, 0), ω (c, 0), c, ω (c, 1), π (c, 1)] := by
  simp [exList, hc, hca]

theorem exList_R {a b : ℕ} {H : Finset ℕ} (π ω : ℕ × ℕ → ℕ) {c : ℕ} (hc : c ∉ H) (hca : c ≠ a) :
    exList a b H π ω c = [c] := by
  simp [exList, hc, hca]

theorem long_cycle {n : ℕ} (hn : N₀ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hD : 70 * (Estar n \ A).card ≤ n) {a b : ℕ} (haA : a ∈ A) (hbA : b ∈ A)
    (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) (hab : a ≠ b) (hcop : Nat.Coprime a b)
    (haU : Undamaged n A a) (hbU : Undamaged n A b)
    (X1 : Finset ℕ) (hX1A : X1 ⊆ A) (hX1odd : ∀ x ∈ X1, x % 2 = 1)
    (hX1U : ∀ x ∈ X1, Undamaged n A x) (haX : a ∉ X1) (hbX : b ∉ X1) (l : ℕ)
    (hX1card : X1.card = l - 1) (hlo : l ≤ o n)
    (hpart : 2 * (X1.filter (fun z => rho z < 14 / 25)).card + 2 ≤
      (X1.filter (fun z => 3 / 4 ≤ rho z)).card)
    (hl : 4 + 2 * (X1.filter (fun z => rho z < 14 / 25)).card ≤ l)
    (hH : ((X1.filter (fun z => rho z < 14 / 25)).card : ℝ) ≤ n / 1000) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  classical
  set H1 := X1.filter (fun z => rho z < 14 / 25) with hH1
  set Ey1 := X1.filter (fun z => 3 / 4 ≤ rho z) with hEy1
  have hH1X : H1 ⊆ X1 := Finset.filter_subset _ _
  have hEyX : Ey1 ⊆ X1 := Finset.filter_subset _ _
  have hHE : ∀ z ∈ H1, z ∉ Ey1 := by
    intro z hz hz'
    have h1 := (Finset.mem_filter.1 hz).2
    have h2 := (Finset.mem_filter.1 hz').2
    linarith
  have haH : a ∉ H1 := fun h => haX (hH1X h)
  have hbH : b ∉ H1 := fun h => hbX (hH1X h)
  have hX1I : ∀ x ∈ X1, x ∈ Icc 1 n := fun x hx => hA (hX1A hx)
  have haI : a ∈ Icc 1 n := hA haA
  have hbI : b ∈ Icc 1 n := hA hbA
  have hEyrho : ∀ y ∈ Ey1, 3 / 4 ≤ rho y := fun y hy => (Finset.mem_filter.1 hy).2
  have hHI : H1 ⊆ Icc 1 n := fun z hz => hX1I z (hH1X hz)
  -- slots
  set SS : Finset (ℕ × ℕ) := {(a, 0), (b, 1)} ∪ H1 ×ˢ {0, 1} with hSS
  have hSSdisj : Disjoint ({(a, 0), (b, 1)} : Finset (ℕ × ℕ)) (H1 ×ˢ {0, 1}) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact haH (Finset.mem_product.1 hs').1
    · exact hbH (Finset.mem_product.1 hs').1
  have hSScard : SS.card = 2 * H1.card + 2 := by
    rw [hSS, Finset.card_union_of_disjoint hSSdisj, Finset.card_product,
      Finset.card_pair_eq_two_iff.2 (by simp), Finset.card_pair_eq_two_iff.2 (by norm_num)]
    ring
  have ha0 : (a, 0) ∈ SS := by simp [hSS]
  have hb1 : (b, 1) ∈ SS := by simp [hSS]
  have hc0 : ∀ c ∈ H1, (c, 0) ∈ SS := fun c hc => by simp [hSS, hc]
  have hc1 : ∀ c ∈ H1, (c, 1) ∈ SS := fun c hc => by simp [hSS, hc]
  have hSSown : ∀ s ∈ SS, s.1 = a ∨ s.1 = b ∨ s.1 ∈ H1 := by
    intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_product.1 h).1)
  have hSSprop : ∀ s ∈ SS, s.1 ∈ Icc 1 n ∧ s.1 % 2 = 1 ∧ Undamaged n A s.1 := by
    intro s hs
    rcases hSSown s hs with h | h | h
    · rw [h]; exact ⟨haI, ha2, haU⟩
    · rw [h]; exact ⟨hbI, hb2, hbU⟩
    · exact ⟨hX1I _ (hH1X h), hX1odd _ (hH1X h), hX1U _ (hH1X h)⟩
  -- partners
  obtain ⟨π, hπ, hπinj⟩ := greedy_choice SS (fun _ => (0 : ℕ)) (fun _ => Ey1) (by
    intro i _
    rw [Finset.filter_true_of_mem (fun _ _ => le_refl _), hSScard]
    exact hpart)
  have hπX : ∀ s ∈ SS, π s ∈ X1 := fun s hs => hEyX (hπ s hs)
  have hπodd : ∀ s ∈ SS, π s % 2 = 1 := fun s hs => hX1odd _ (hπX s hs)
  have hπI : ∀ s ∈ SS, π s ∈ Icc 1 n := fun s hs => hX1I _ (hπX s hs)
  -- connectors
  obtain ⟨ω, hω, hωinj⟩ := greedy_choice SS (fun s => rho s.1)
      (fun s => NA n A (Nat.lcm (π s) s.1)) (by
    intro s hs
    obtain ⟨hsI, hs2, hsU⟩ := hSSprop s hs
    have hmaster := NA_card_master (A := A) hn (hπI s hs) hsI (hπodd s hs) hs2
      (hEyrho _ (hπ s hs)) hsU
    have hsub : SS.filter (fun j => rho j.1 ≤ rho s.1) ⊆
        {(a, 0), (b, 1)} ∪ (H1.filter (fun z => rho z ≤ rho s.1)) ×ˢ {0, 1} := by
      intro j hj
      obtain ⟨hjS, hjr⟩ := Finset.mem_filter.1 hj
      rcases Finset.mem_union.1 hjS with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨h1, h2⟩ := Finset.mem_product.1 h
        exact Finset.mem_union_right _ (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨h1, hjr⟩, h2⟩)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le ({(a, 0), (b, 1)} : Finset (ℕ × ℕ))
      ((H1.filter (fun z => rho z ≤ rho s.1)) ×ˢ ({0, 1} : Finset ℕ))
    rw [Finset.card_product, (Finset.card_pair_eq_two_iff (a := (0 : ℕ)) (b := 1)).2
      (by norm_num)] at hc2
    have hc3 : ({(a, 0), (b, 1)} : Finset (ℕ × ℕ)).card ≤ 2 := Finset.card_le_two
    have hfil := card_filter_rho_le' hHI hH (rho_pos s.1)
    have hfin : ((SS.filter (fun j => rho j.1 ≤ rho s.1)).card : ℝ) ≤
        2 + 2 * ((H1.filter (fun z => rho z ≤ rho s.1)).card : ℝ) := by
      exact_mod_cast (by omega : (SS.filter (fun j => rho j.1 ≤ rho s.1)).card ≤
        2 + 2 * (H1.filter (fun z => rho z ≤ rho s.1)).card)
    have : ((SS.filter (fun j => rho j.1 ≤ rho s.1)).card : ℝ) ≤
        ((NA n A (Nat.lcm (π s) s.1)).card : ℝ) := by
      linarith
    exact_mod_cast this)
  have hωNA : ∀ s ∈ SS, ω s ∈ Nstar n (Nat.lcm (π s) s.1) ∧ ω s ∈ A :=
    fun s hs => mem_NA.1 (hω s hs)
  have hωeven : ∀ s ∈ SS, ω s % 2 = 0 := fun s hs =>
    even_of_mem_Estar (mem_Nstar.1 (hωNA s hs).1).1
  set PI := SS.image π with hPI
  set WI := SS.image ω with hWI
  have hPIcard : PI.card = SS.card := Finset.card_image_of_injOn hπinj
  have hWIcard : WI.card = SS.card := Finset.card_image_of_injOn hωinj
  have hPIE : PI ⊆ Ey1 := by
    intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hπ s hs
  have hWIev : ∀ v ∈ WI, v % 2 = 0 := by
    intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hωeven s hs
  have hWIA : ∀ v ∈ WI, v ∈ Estar n ∧ v ∈ A := by
    intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨(mem_Nstar.1 (hωNA s hs).1).1, (hωNA s hs).2⟩
  have hPIodd : ∀ v ∈ PI, v % 2 = 1 := fun v hv => hX1odd v (hEyX (hPIE hv))
  -- the remaining odd vertices
  set R := X1 \ (H1 ∪ PI) with hR
  set X' := insert a (H1 ∪ R) with hX'
  have hHPI : Disjoint H1 PI := by
    rw [Finset.disjoint_left]; intro z hz hz'; exact hHE z hz (hPIE hz')
  have hRsub : H1 ∪ PI ⊆ X1 := Finset.union_subset hH1X (fun v hv => hEyX (hPIE hv))
  have hRcard : R.card = (l - 1) - (H1.card + SS.card) := by
    rw [hR, Finset.card_sdiff_of_subset hRsub, Finset.card_union_of_disjoint hHPI, hPIcard,
      hX1card]
  have hHR : Disjoint H1 R := by
    rw [Finset.disjoint_left]; intro z hz hz'
    exact (Finset.mem_sdiff.1 hz').2 (Finset.mem_union_left _ hz)
  have haHR : a ∉ H1 ∪ R := by
    intro h; rcases Finset.mem_union.1 h with h | h
    · exact haH h
    · exact haX (Finset.mem_sdiff.1 h).1
  have hX'card : X'.card = 1 + H1.card + R.card := by
    rw [hX', Finset.card_insert_of_notMem haHR, Finset.card_union_of_disjoint hHR]; ring
  have hRX : ∀ c ∈ R, c ∈ X1 ∧ c ∉ H1 ∧ c ∉ PI := by
    intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hc
    exact ⟨h1, fun h => h2 (Finset.mem_union_left _ h), fun h => h2 (Finset.mem_union_right _ h)⟩
  have hX'mem : ∀ c ∈ X', c = a ∨ (c ∈ H1 ∧ c ≠ a) ∨ (c ∈ R ∧ c ≠ a ∧ c ∉ H1) := by
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact Or.inl rfl
    · have hca : c ≠ a := fun h => haHR (h ▸ hc)
      rcases Finset.mem_union.1 hc with h | h
      · exact Or.inr (Or.inl ⟨h, hca⟩)
      · exact Or.inr (Or.inr ⟨h, hca, (hRX c h).2.1⟩)
  set ex := exList a b H1 π ω with hex
  -- labels
  let own : ℕ × ℕ → ℕ := fun s => if s.1 = b then a else s.1
  let lab : ℕ → ℕ := fun v =>
    if v ∈ PI then own (Function.invFunOn π (SS : Set (ℕ × ℕ)) v)
    else if v ∈ WI then own (Function.invFunOn ω (SS : Set (ℕ × ℕ)) v)
    else if v = b then a else v
  have hlabπ : ∀ s ∈ SS, lab (π s) = own s := by
    intro s hs
    have hmem : π s ∈ PI := Finset.mem_image_of_mem π hs
    simp only [lab, hmem, ite_true]
    rw [hπinj.leftInvOn_invFunOn (Finset.mem_coe.2 hs)]
  have hlabω : ∀ s ∈ SS, lab (ω s) = own s := by
    intro s hs
    have hmem : ω s ∈ WI := Finset.mem_image_of_mem ω hs
    have hnot : ω s ∉ PI := fun h => by have := hPIodd _ h; have := hωeven s hs; omega
    simp only [lab, hnot, hmem, ite_true, ite_false]
    rw [hωinj.leftInvOn_invFunOn (Finset.mem_coe.2 hs)]
  have hlabc : ∀ v, v % 2 = 1 → v ∉ PI → lab v = if v = b then a else v := by
    intro v hv hvP
    have : v ∉ WI := fun h => by have := hWIev v h; omega
    simp only [lab, hvP, this, ite_false]
  have haPI : a ∉ PI := fun h => haX (hEyX (hPIE h))
  have hbPI : b ∉ PI := fun h => hbX (hEyX (hPIE h))
  have hlab : ∀ c ∈ X', ∀ v ∈ ex c, lab v = c := by
    intro c hc v hv
    rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
    · rw [hex, exList_a] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hlabπ _ ha0]; simp [own]
      · rw [hlabω _ ha0]; simp [own]
      · rw [hlabc _ ha2 haPI]; simp [hab]
      · rw [hlabc _ hb2 hbPI]; simp
      · rw [hlabω _ hb1]; simp [own]
      · rw [hlabπ _ hb1]; simp [own]
    · rw [hex, exList_H π ω hcH hca] at hv
      have hcb : c ≠ b := fun h => hbH (h ▸ hcH)
      have hcPI : c ∉ PI := fun h => hHE c hcH (hPIE h)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · rw [hlabπ _ (hc0 c hcH)]; simp [own, hcb]
      · rw [hlabω _ (hc0 c hcH)]; simp [own, hcb]
      · rw [hlabc _ (hX1odd _ (hH1X hcH)) hcPI]; simp [hcb]
      · rw [hlabω _ (hc1 c hcH)]; simp [own, hcb]
      · rw [hlabπ _ (hc1 c hcH)]; simp [own, hcb]
    · rw [hex, exList_R π ω hcH hca] at hv
      simp only [List.mem_singleton] at hv
      subst hv
      have hvb : v ≠ b := fun h => hbX (h ▸ (hRX v hcR).1)
      rw [hlabc _ (hX1odd _ (hRX v hcR).1) (hRX v hcR).2.2]; simp [hvb]
  -- every vertex of a path is odd and in `A`, or is a connector
  have hclass : ∀ c ∈ X', ∀ v ∈ ex c, (v % 2 = 1 ∧ v ∈ A ∧ v ∈ Icc 1 n) ∨ v ∈ WI := by
    intro c hc v hv
    have hπA : ∀ s ∈ SS, π s % 2 = 1 ∧ π s ∈ A ∧ π s ∈ Icc 1 n :=
      fun s hs => ⟨hπodd s hs, hX1A (hπX s hs), hπI s hs⟩
    rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
    · rw [hex, exList_a] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hπA _ ha0)
      · exact Or.inr (Finset.mem_image_of_mem ω ha0)
      · exact Or.inl ⟨ha2, haA, haI⟩
      · exact Or.inl ⟨hb2, hbA, hbI⟩
      · exact Or.inr (Finset.mem_image_of_mem ω hb1)
      · exact Or.inl (hπA _ hb1)
    · rw [hex, exList_H π ω hcH hca] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hπA _ (hc0 c hcH))
      · exact Or.inr (Finset.mem_image_of_mem ω (hc0 c hcH))
      · exact Or.inl ⟨hX1odd _ (hH1X hcH), hX1A (hH1X hcH), hX1I _ (hH1X hcH)⟩
      · exact Or.inr (Finset.mem_image_of_mem ω (hc1 c hcH))
      · exact Or.inl (hπA _ (hc1 c hcH))
    · rw [hex, exList_R π ω hcH hca] at hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact Or.inl ⟨hX1odd _ (hRX v hcR).1, hX1A (hRX v hcR).1, hX1I _ (hRX v hcR).1⟩
  -- the pool
  set B := ((Estar n).filter (· ∈ A)) \ WI with hB
  have hBA : B ⊆ A := fun v hv => (Finset.mem_filter.1 (Finset.mem_sdiff.1 hv).1).2
  have hEstar_card : (Estar n).card = n / 2 - n / 6 := by
    rw [← Cnt_empty_eq_card_Estar, Cnt_empty]
  have hBcard : B.card ≤ n / 2 - n / 6 := by
    rw [← hEstar_card]
    exact Finset.card_le_card (fun v hv => (Finset.mem_filter.1 (Finset.mem_sdiff.1 hv).1).1)
  have hon : o n ≤ n / 6 + 1 := by unfold o; omega
  have hsize : H1.card + SS.card ≤ l - 1 := by
    have := Finset.card_le_card hRsub
    rw [Finset.card_union_of_disjoint hHPI, hPIcard, hX1card] at this
    exact this
  have hWc : (WI.card : ℝ) ≤ n / 500 + 2 := by
    rw [hWIcard, hSScard]; push_cast; linarith
  have hdeg_of : ∀ c ∈ X', ∀ p q, (ex c).headD 0 = p → (ex c).getLastD 0 = q →
      p ∈ Icc 1 n → q ∈ Icc 1 n → p % 2 = 1 → q % 2 = 1 → 14 / 25 ≤ rho (Nat.lcm p q) →
      n / 6 + 2 ≤ (B.filter (fun β => EndRel ex c β)).card := by
    intro c _ p q hp hq hpI hqI hp2 hq2 hrho
    have h1 := deg_master hn hpI hqI hp2 hq2 hrho hD WI hWc
    refine h1.trans (Finset.card_le_card ?_)
    intro β hβ
    obtain ⟨hβN, hβnot⟩ := Finset.mem_sdiff.1 hβ
    have hβE := (mem_Nstar.1 hβN).1
    have hβA : β ∈ A := by
      by_contra h
      exact hβnot (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hβE, h⟩))
    have hβW : β ∉ WI := fun h => hβnot (Finset.mem_union_right _ h)
    refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hβE, hβA⟩, hβW⟩, ?_⟩
    have := coprime_of_mem_Nstar_lcm hβN
    unfold EndRel; rw [hp, hq]; exact ⟨this.2.symm, this.1⟩
  have hrho_easy : ∀ s ∈ SS, ∀ s' ∈ SS, 14 / 25 ≤ rho (Nat.lcm (π s) (π s')) := by
    intro s hs s' hs'
    have h1 := hEyrho _ (hπ s hs)
    have h2 := hEyrho _ (hπ s' hs')
    have h0 : π s ≠ 0 := by have := (Finset.mem_Icc.1 (hπI s hs)).1; omega
    have h0' : π s' ≠ 0 := by have := (Finset.mem_Icc.1 (hπI s' hs')).1; omega
    have := rho_lcm_ge h0 h0'
    nlinarith
  -- apply the assembly lemma
  have hcyc := assembly ex A X' B (n / 6 + 2)
    (by -- nonempty paths
      intro c hc
      rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
      · rw [hex, exList_a]; simp
      · rw [hex, exList_H π ω hcH hca]; simp
      · rw [hex, exList_R π ω hcH hca]; simp)
    (by -- chains
      intro c hc
      rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
      · rw [hex, exList_a]
        exact chain_closing (hωNA _ ha0).1 (hωNA _ hb1).1 hcop
      · rw [hex, exList_H π ω hcH hca]
        exact chain_gadget (hωNA _ (hc0 c hcH)).1 (hωNA _ (hc1 c hcH)).1
      · rw [hex, exList_R π ω hcH hca]; exact List.IsChain.singleton _)
    (by -- no repetition inside a path
      intro c hc
      rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
      · rw [hex, exList_a]
        refine nodup_closing (hπodd _ ha0) ha2 hb2 (hπodd _ hb1) (hωeven _ ha0) (hωeven _ hb1)
          (fun h => by have := hπinj (Finset.mem_coe.2 ha0) (Finset.mem_coe.2 hb1) h; simp at this)
          (fun h => by have := hωinj (Finset.mem_coe.2 ha0) (Finset.mem_coe.2 hb1) h; simp at this)
          hab (fun h => haX (h ▸ hπX _ ha0)) (fun h => haX (h ▸ hπX _ hb1))
          (fun h => hbX (h ▸ hπX _ ha0)) (fun h => hbX (h ▸ hπX _ hb1))
      · rw [hex, exList_H π ω hcH hca]
        refine nodup_gadget (hπodd _ (hc0 c hcH)) (hX1odd _ (hH1X hcH)) (hπodd _ (hc1 c hcH))
          (hωeven _ (hc0 c hcH)) (hωeven _ (hc1 c hcH))
          (fun h => by
            have := hπinj (Finset.mem_coe.2 (hc0 c hcH)) (Finset.mem_coe.2 (hc1 c hcH)) h
            simp at this)
          (fun h => by
            have := hωinj (Finset.mem_coe.2 (hc0 c hcH)) (Finset.mem_coe.2 (hc1 c hcH)) h
            simp at this)
          (fun h => hHE c hcH (h ▸ hπ _ (hc0 c hcH))) (fun h => hHE c hcH (h ▸ hπ _ (hc1 c hcH)))
      · rw [hex, exList_R π ω hcH hca]; exact List.nodup_singleton _)
    (by -- disjoint paths
      intro c hc c' hc' hcc' v hv hv'
      exact hcc' ((hlab c hc v hv).symm.trans (hlab c' hc' v hv')))
    (by -- paths avoid the pool
      intro c hc v hv hvB
      rcases hclass c hc v hv with ⟨hv2, -, -⟩ | hvW
      · have := even_of_mem_Estar (Finset.mem_filter.1 (Finset.mem_sdiff.1 hvB).1).1; omega
      · exact (Finset.mem_sdiff.1 hvB).2 hvW)
    (by -- paths lie in `A`
      intro c hc v hv
      rcases hclass c hc v hv with ⟨-, hvA, -⟩ | hvW
      · exact hvA
      · exact (hWIA v hvW).2)
    hBA
    (by rw [hX'card, hRcard, hSScard]; rw [hSScard] at hsize; omega)
    (by rw [hX'card, hRcard, hSScard]; rw [hSScard] at hsize; omega)
    (by omega)
    (by -- degrees
      intro c hc
      rcases hX'mem c hc with rfl | ⟨hcH, hca⟩ | ⟨hcR, hca, hcH⟩
      · exact hdeg_of _ hc (π (c, 0)) (π (b, 1)) (by rw [hex, exList_a]; rfl)
          (by rw [hex, exList_a]; rfl) (hπI _ ha0) (hπI _ hb1) (hπodd _ ha0) (hπodd _ hb1)
          (hrho_easy _ ha0 _ hb1)
      · exact hdeg_of _ hc (π (c, 0)) (π (c, 1)) (by rw [hex, exList_H π ω hcH hca]; rfl)
          (by rw [hex, exList_H π ω hcH hca]; rfl) (hπI _ (hc0 c hcH)) (hπI _ (hc1 c hcH))
          (hπodd _ (hc0 c hcH)) (hπodd _ (hc1 c hcH)) (hrho_easy _ (hc0 c hcH) _ (hc1 c hcH))
      · have hcX := (hRX c hcR).1
        refine hdeg_of _ hc c c (by rw [hex, exList_R π ω hcH hca]; rfl)
          (by rw [hex, exList_R π ω hcH hca]; rfl) (hX1I _ hcX) (hX1I _ hcX) (hX1odd _ hcX)
          (hX1odd _ hcX) ?_
        rw [Nat.lcm_self]
        by_contra h
        push Not at h
        exact hcH (Finset.mem_filter.2 ⟨hcX, h⟩))
  have hsum : ∑ c ∈ X', (ex c).length = 6 + 5 * H1.card + R.card := by
    rw [hX', Finset.sum_insert haHR, Finset.sum_union hHR]
    have e1 : (ex a).length = 6 := by rw [hex, exList_a]; rfl
    have e2 : ∑ c ∈ H1, (ex c).length = ∑ c ∈ H1, 5 :=
      Finset.sum_congr rfl (fun c hc => by
        rw [hex, exList_H π ω hc (fun h => haH (by rw [← h]; exact hc))]; rfl)
    have e3 : ∑ c ∈ R, (ex c).length = ∑ c ∈ R, 1 :=
      Finset.sum_congr rfl (fun c hc => by
        rw [hex, exList_R π ω (hRX c hc).2.1 (fun h => haX (by rw [← h]; exact (hRX c hc).1))]
        rfl)
    rw [e1, e2, e3, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsum, hX'card, hRcard, hSScard] at hcyc
  rw [hSScard] at hsize
  convert hcyc using 1
  omega

end ErdosSar
