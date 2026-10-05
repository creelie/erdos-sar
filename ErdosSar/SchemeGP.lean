import ErdosSar.GPPath

/-!
# The construction with pool `E* ∩ A` and one giant path

Let `k` be the target number of pool vertices per gadget. We take a coprime pair `wQ, g₂` of odd
elements of large density with `wQ` a unit, a third odd element `g₁`, further units
`w₀, …, w_{Q-2}`, an element `e₁ ∈ E* ∩ A` joining `g₁` to `w₀`, and multiples `y_i` of `6` in
`A` joining consecutive units. Together with `l - 1 - Q` single odd vertices, the giant path
`g₁, e₁, w₀, y₀, …, y_{Q-2}, w_{Q-1}, g₂` is closed into a cycle of length `2l + 1` through the
pool `(E* ∩ A) \ {e₁}` by the assembly lemma. Here `Q = 1` if `l ≤ k` and `Q = l - k` otherwise.
-/

namespace ErdosSar

open Finset

theorem card_NA_ge (n m : ℕ) (A : Finset ℕ) :
    ((Nstar n m).card : ℝ) ≤ (NA n A m).card + (Estar n \ A).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Nstar n m) (fun w => w ∈ A)
  have h2 : ((Nstar n m).filter (fun w => w ∉ A)).card ≤ (Estar n \ A).card :=
    Finset.card_le_card (fun w hw => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_sdiff.2 ⟨(mem_Nstar.1 h1).1, h2⟩)
  have : (Nstar n m).card ≤ (NA n A m).card + (Estar n \ A).card := by
    unfold NA; omega
  exact_mod_cast this

/-- Elements of `E* ∩ A` coprime to two odd numbers `p, q` whose `lcm` has density `≥ θ`. -/
theorem card_NA_ge_big {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} {p q : ℕ} (hp : p ∈ Icc 1 n)
    (hq : q ∈ Icc 1 n) (hp2 : p % 2 = 1) (hq2 : q % 2 = 1) {θ : ℝ}
    (hρ : θ ≤ rho (Nat.lcm p q)) :
    (n : ℝ) / 3 * θ - n / 10 ^ 6 - (Estar n \ A).card ≤ (NA n A (Nat.lcm p q)).card := by
  have h1 := card_Nstar_ge_big hn (odd_lcm hp2 hq2) (lcm_le_sq hp hq)
  have h2 := card_NA_ge n (Nat.lcm p q) A
  have h3 : (n : ℝ) / 3 * θ ≤ n / 3 * rho (Nat.lcm p q) :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  linarith

/-- Degree of a gadget with odd ends `p, q` into the pool `(E* ∩ A) \ {e₁}`. -/
theorem deg_pool_GP {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} {p q e1 : ℕ} (hp : p ∈ Icc 1 n)
    (hq : q ∈ Icc 1 n) (hp2 : p % 2 = 1) (hq2 : q % 2 = 1) {θ : ℝ}
    (hρ : θ ≤ rho (Nat.lcm p q)) {k : ℕ}
    (H9 : (k : ℝ) + (Estar n \ A).card + 1 + n / 10 ^ 6 ≤ n / 3 * θ) :
    k ≤ ((((Estar n).filter (· ∈ A)).erase e1).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card := by
  have h1 := card_NA_ge_big (A := A) hn hp hq hp2 hq2 hρ
  have hsub : (NA n A (Nat.lcm p q)).erase e1 ⊆ ((((Estar n).filter (· ∈ A)).erase e1).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)) := by
    intro β hβ
    obtain ⟨hβe, hβ'⟩ := Finset.mem_erase.1 hβ
    obtain ⟨hβN, hβA⟩ := mem_NA.1 hβ'
    have hc := coprime_of_mem_Nstar_lcm hβN
    exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hβe, Finset.mem_filter.2
      ⟨(mem_Nstar.1 hβN).1, hβA⟩⟩, hc.2.symm, hc.1⟩
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.pred_card_le_card_erase (s := NA n A (Nat.lcm p q)) (a := e1)
  have h4 : ((NA n A (Nat.lcm p q)).card : ℝ) ≤ ((((Estar n).filter (· ∈ A)).erase e1).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card + 1 := by
    exact_mod_cast (by omega : (NA n A (Nat.lcm p q)).card ≤ ((((Estar n).filter (· ∈ A)).erase
      e1).filter (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card + 1)
  have : (k : ℝ) ≤ ((((Estar n).filter (· ∈ A)).erase e1).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card := by linarith
  exact_mod_cast this

theorem symRes_zero : SymRes {0} := by
  refine ⟨by simp, by simp⟩

/-- **The giant-path construction.** -/
theorem gp_cycle {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    {l k : ℕ} (hl2 : 2 ≤ l) (hk2 : 2 ≤ k) {s t1 θ θw sw : ℝ}
    (ht0 : 0 ≤ t1) (hθw0 : 0 ≤ θw) (hsws : sw ≤ s) (hswθ : k < l → sw ≤ θw)
    (H1 : o n + 1 ≤ (Good A s).card) (H2 : 3 ≤ (Good A t1).card) (H3 : θ ≤ t1 * s)
    (H4 : k < l → l - k + 2 ≤ (GoodU A θw).card)
    (H5 : ((Estar n \ A).card : ℝ) + 1 + n / 10 ^ 6 ≤ n / 3 * (t1 * sw))
    (H6 : k < l → ((l - k - 1 : ℕ) : ℝ) + (M6 n \ A).card + n / 10 ^ 6 ≤ n / 6 * (θw * sw))
    (H7 : l + 1 ≤ (Good A θ).card)
    (H8 : (Estar n).card + 1 ≤ 2 * k + (Estar n \ A).card)
    (H9 : (k : ℝ) + (Estar n \ A).card + 1 + n / 10 ^ 6 ≤ n / 3 * θ) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  classical
  have hn13 : 13 ≤ n := le_trans (by unfold N₁; norm_num) hn
  have hGI : ∀ t, ∀ z ∈ Good A t, z ∈ Icc 1 n := fun t z hz => hA (mem_Good.1 hz).1
  have hGUI : ∀ t, ∀ z ∈ GoodU A t, z ∈ Icc 1 n := fun t z hz => hA (mem_GoodU.1 hz).1
  have hI0 : ∀ z ∈ Icc 1 n, z ≠ 0 := fun z hz => by have := (Finset.mem_Icc.1 hz).1; omega
  -- the coprime pair, with `wQ` a unit
  obtain ⟨a, ha, b, hb, hab, hcop⟩ := coprime_pair hn13 (Good A s) (fun z hz => hGI s z hz)
    (fun z hz => Nat.odd_iff.2 (mem_Good.1 hz).2.1) H1
  obtain ⟨wQ, g2, hwQ, hg2, hwg, hcopwg, hwQu⟩ : ∃ wQ g2, wQ ∈ Good A s ∧ g2 ∈ Good A s ∧
      wQ ≠ g2 ∧ Nat.Coprime wQ g2 ∧ (wQ % 6 = 1 ∨ wQ % 6 = 5) := by
    have ha2 := (mem_Good.1 ha).2.1
    have hb2 := (mem_Good.1 hb).2.1
    by_cases h3 : a % 3 = 0
    · refine ⟨b, a, hb, ha, hab.symm, hcop.symm, ?_⟩
      have : b % 3 ≠ 0 := fun h3' => by
        have h := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mod_eq_zero h3) hcop
        have h' := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mod_eq_zero h3') h
        norm_num at h'
      omega
    · exact ⟨a, b, ha, hb, hab, hcop, by omega⟩
  obtain ⟨hwQA, hwQ2, hwQρ⟩ := mem_Good.1 hwQ
  obtain ⟨hg2A, hg22, hg2ρ⟩ := mem_Good.1 hg2
  -- the third odd element
  obtain ⟨g1, hg1, hg1w, hg1g2⟩ : ∃ g1 ∈ Good A t1, g1 ≠ wQ ∧ g1 ≠ g2 := by
    have h := Finset.le_card_sdiff ({wQ, g2} : Finset ℕ) (Good A t1)
    have h2 : ({wQ, g2} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    obtain ⟨g1, hg1⟩ := Finset.card_pos.1 (show 0 < (Good A t1 \ {wQ, g2}).card by omega)
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hg1
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact ⟨g1, h1, h2.1, h2.2⟩
  obtain ⟨hg1A, hg12, hg1ρ⟩ := mem_Good.1 hg1
  have hg1I := hA hg1A
  have hg2I := hA hg2A
  have hwQI := hA hwQA
  have hρG : θ ≤ rho (Nat.lcm g1 g2) := by
    have := rho_lcm_ge_of (hI0 _ hg1I) (hI0 _ hg2I) ht0 hg1ρ hg2ρ
    linarith


  have hEcard : ((Estar n).filter (· ∈ A)).card + (Estar n \ A).card = (Estar n).card := by
    have h := Finset.card_filter_add_card_filter_not (s := Estar n) (fun w => w ∈ A)
    have e : (Estar n).filter (fun w => w ∉ A) = Estar n \ A := by ext; simp
    rw [e] at h; exact h
  have hpos : ∀ X : Finset ℕ, (1 : ℝ) ≤ X.card → ∃ x, x ∈ X := fun X h => by
    have : 1 ≤ X.card := by exact_mod_cast h
    exact Finset.card_pos.1 (by omega)
  rcases (by omega : l = 2 ∨ 3 ≤ l) with rfl | hl3
  · -- the five-cycle `g₁, e₁, wQ, g₂, β`
    have hρe : t1 * sw ≤ rho (Nat.lcm g1 wQ) :=
      rho_lcm_ge_of (hI0 _ hg1I) (hI0 _ hwQI) ht0 hg1ρ (hsws.trans hwQρ)
    have hNA := card_NA_ge_big (A := A) hn hg1I hwQI hg12 hwQ2 hρe
    obtain ⟨e1, he1⟩ := hpos _ (by linarith)
    obtain ⟨he1N, he1A⟩ := mem_NA.1 he1
    have he1c := coprime_of_mem_Nstar_lcm he1N
    have he1E := even_of_mem_Estar (mem_Nstar.1 he1N).1
    have hdeg := deg_pool_GP (A := A) (e1 := e1) hn hg1I hg2I hg12 hg22 hρG H9
    obtain ⟨β, hβ⟩ := Finset.card_pos.1 (show 0 < _ from lt_of_lt_of_le (by omega) hdeg)
    obtain ⟨hβB, hβg2, hβg1⟩ := Finset.mem_filter.1 hβ
    obtain ⟨hβe, hβ'⟩ := Finset.mem_erase.1 hβB
    obtain ⟨hβE, hβA⟩ := Finset.mem_filter.1 hβ'
    have hβev := even_of_mem_Estar hβE
    have := hasCycle_of_list A g1 [e1, wQ, g2, β]
      (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
          not_or, not_false_eq_true, and_true]
        omega)
      (by simp)
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
      (by
        simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
          List.IsChain.singleton, and_true]
        exact ⟨he1c.1.symm, he1c.2, hcopwg, hβg2, hβg1⟩)
    simpa using this
  -- the general case
  set Q := if l ≤ k then 1 else l - k with hQdef
  have hQ1 : 1 ≤ Q := by rw [hQdef]; split_ifs <;> omega
  have hQl : Q + 2 ≤ l := by rw [hQdef]; split_ifs <;> omega
  have hQk : l - Q ≤ k := by rw [hQdef]; split_ifs <;> omega
  have hQ2 : 2 ≤ Q → k < l ∧ Q - 1 = l - k - 1 := by rw [hQdef]; split_ifs <;> omega
  -- the units `w₀, …, w_{Q-2}`
  obtain ⟨w', hw'C, hw'inj⟩ := greedy_choice (Finset.range (Q - 1)) (fun _ => (0 : ℕ))
    (fun _ => GoodU A θw \ {g1, g2, wQ}) (by
      intro i hi
      rw [Finset.filter_true_of_mem (fun _ _ => le_refl _), Finset.card_range]
      have hQ2' := hQ2 (by have := Finset.mem_range.1 hi; omega)
      have h := Finset.le_card_sdiff ({g1, g2, wQ} : Finset ℕ) (GoodU A θw)
      have h3 : ({g1, g2, wQ} : Finset ℕ).card ≤ 3 := Finset.card_le_three
      have := H4 hQ2'.1
      omega)
  set w : ℕ → ℕ := fun i => if i < Q - 1 then w' i else wQ with hwdef
  have hw_lt : ∀ i < Q - 1, w i = w' i := fun i hi => by simp [hwdef, hi]
  have hw_last : w (Q - 1) = wQ := by simp [hwdef]
  have hw'mem : ∀ i < Q - 1, w' i ∈ GoodU A θw ∧ w' i ≠ g1 ∧ w' i ≠ g2 ∧ w' i ≠ wQ := by
    intro i hi
    have h := hw'C i (Finset.mem_range.2 hi)
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact ⟨h1, h2.1, h2.2.1, h2.2.2⟩
  have hwprop : ∀ i < Q, w i ∈ A ∧ (w i % 6 = 1 ∨ w i % 6 = 5) ∧ sw ≤ rho (w i) ∧
      w i ≠ g1 ∧ w i ≠ g2 := by
    intro i hi
    rcases (by omega : i < Q - 1 ∨ i = Q - 1) with h | rfl
    · rw [hw_lt i h]
      obtain ⟨hG, h1, h2, -⟩ := hw'mem i h
      obtain ⟨hA', hu, hρ⟩ := mem_GoodU.1 hG
      exact ⟨hA', hu, (hswθ (hQ2 (by omega)).1).trans hρ, h1, h2⟩
    · rw [hw_last]
      exact ⟨hwQA, hwQu, hsws.trans hwQρ, fun h => hg1w h.symm, hwg⟩
  have hwodd : ∀ i < Q, w i % 2 = 1 := fun i hi => by
    rcases (hwprop i hi).2.1 with h | h <;> omega
  have hwθ : ∀ i < Q - 1, θw ≤ rho (w i) := fun i hi => by
    rw [hw_lt i hi]; exact (mem_GoodU.1 (hw'mem i hi).1).2.2
  have hwinj : ∀ i < Q, ∀ i' < Q, w i = w i' → i = i' := by
    intro i hi i' hi' h
    rcases (by omega : i < Q - 1 ∨ i = Q - 1) with h1 | rfl <;>
    rcases (by omega : i' < Q - 1 ∨ i' = Q - 1) with h1' | h1'
    · rw [hw_lt i h1, hw_lt i' h1'] at h
      exact hw'inj (Finset.mem_coe.2 (Finset.mem_range.2 h1))
        (Finset.mem_coe.2 (Finset.mem_range.2 h1')) h
    · rw [h1', hw_lt i h1, hw_last] at h; exact absurd h (hw'mem i h1).2.2.2
    · rw [hw_lt i' h1', hw_last] at h; exact absurd h.symm (hw'mem i' h1').2.2.2
    · omega
  -- the element `e₁`
  have hw0 := hwprop 0 (by omega)
  have hρe : t1 * sw ≤ rho (Nat.lcm g1 (w 0)) :=
    rho_lcm_ge_of (hI0 _ hg1I) (hI0 _ (hA hw0.1)) ht0 hg1ρ hw0.2.2.1
  have hNA := card_NA_ge_big (A := A) hn hg1I (hA hw0.1) hg12 (hwodd 0 (by omega)) hρe
  obtain ⟨e1, he1⟩ := hpos _ (by linarith)
  obtain ⟨he1N, he1A⟩ := mem_NA.1 he1
  have he1c := coprime_of_mem_Nstar_lcm he1N
  have he1E := (mem_Nstar.1 he1N).1
  have he16 := (mem_Estar.1 he1E).2
  -- the multiples of `6`
  obtain ⟨y, hyC, hyinj⟩ := greedy_choice (Finset.range (Q - 1)) (fun _ => (0 : ℕ))
    (fun i => ((M6 n).filter (· ∈ A)).filter
      (fun z => Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))) (by
      intro i hi
      rw [Finset.filter_true_of_mem (fun _ _ => le_refl _), Finset.card_range]
      have hi' := Finset.mem_range.1 hi
      obtain ⟨hkl, hQeq⟩ := hQ2 (by omega)
      have hH6 := H6 hkl
      have hwi := hwprop i (by omega)
      have hwi1 := hwprop (i + 1) (by omega)
      have hm0 : Nat.lcm (w i) (w (i + 1)) ≠ 0 :=
        Nat.lcm_ne_zero (hI0 _ (hA hwi.1)) (hI0 _ (hA hwi1.1))
      have hmn := lcm_le_sq (hA hwi.1) (hA hwi1.1)
      have hu := lcm_unit hwi.2.1 hwi1.2.1
      have hcnt := card_class_coprime_ge_big (n := n) (R := {0}) symRes_zero hn hm0 hmn
        (fun h => absurd h hu.1) (fun h => absurd h hu.2)
      have hρm : θw * sw ≤ rho (Nat.lcm (w i) (w (i + 1))) :=
        rho_lcm_ge_of (hI0 _ (hA hwi.1)) (hI0 _ (hA hwi1.1)) hθw0 (hwθ i (by omega)) hwi1.2.2.1
      have hsub : ((Icc 1 n).filter (fun z => z % 6 ∈ ({0} : Finset ℕ) ∧
          Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))) ⊆
          (((M6 n).filter (· ∈ A)).filter (fun z => Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))) ∪
            (M6 n \ A) := by
        intro z hz
        obtain ⟨hzI, hz6, hzc⟩ := Finset.mem_filter.1 hz
        have hzM : z ∈ M6 n := Finset.mem_filter.2 ⟨hzI, by simpa using hz6⟩
        by_cases hzA : z ∈ A
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzM, hzA⟩, hzc⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hzM, hzA⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        (((M6 n).filter (· ∈ A)).filter (fun z => Nat.Coprime z (Nat.lcm (w i) (w (i + 1)))))
        (M6 n \ A)
      have h3 : (n : ℝ) / 6 * (θw * sw) ≤ (n : ℝ) / 6 * rho (Nat.lcm (w i) (w (i + 1))) :=
        mul_le_mul_of_nonneg_left hρm (by positivity)
      simp only [Finset.card_singleton, Nat.cast_one, mul_one, one_mul] at hcnt
      have h12 : (((Icc 1 n).filter (fun z => z % 6 ∈ ({0} : Finset ℕ) ∧
          Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))).card : ℝ) ≤
          ((((M6 n).filter (· ∈ A)).filter
            (fun z => Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))).card : ℝ) +
            (M6 n \ A).card := by exact_mod_cast h1.trans h2
      have h4 : ((Q - 1 : ℕ) : ℝ) ≤ ((((M6 n).filter (· ∈ A)).filter
          (fun z => Nat.Coprime z (Nat.lcm (w i) (w (i + 1))))).card : ℝ) := by
        rw [hQeq]; linarith
      exact_mod_cast h4)
  have hyprop : ∀ i, i + 1 < Q → y i ∈ A ∧ y i % 6 = 0 ∧ Nat.Coprime (y i) (w i) ∧
      Nat.Coprime (y i) (w (i + 1)) := by
    intro i hi
    have h := hyC i (Finset.mem_range.2 (by omega))
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
    exact ⟨h4, (mem_M6.1 h3).2, Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_left _ _) h2,
      Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_right _ _) h2⟩
  -- the giant path
  set G := gpPath Q g1 e1 g2 w y with hG
  -- the odd vertices of the giant path
  set Wodd := insert g1 (insert g2 (insert wQ ((Finset.range (Q - 1)).image w'))) with hWodd
  have hWoddc : Wodd.card ≤ Q + 2 := by
    have h1 : Wodd.card ≤ (insert g2 (insert wQ ((Finset.range (Q - 1)).image w'))).card + 1 :=
      Finset.card_insert_le _ _
    have h2 := Finset.card_insert_le g2 (insert wQ ((Finset.range (Q - 1)).image w'))
    have h3 := Finset.card_insert_le wQ ((Finset.range (Q - 1)).image w')
    have h4 := Finset.card_image_le (s := Finset.range (Q - 1)) (f := w')
    rw [Finset.card_range] at h4
    omega
  have hg1W : g1 ∈ Wodd := by simp [hWodd]
  have hg2W : g2 ∈ Wodd := by simp [hWodd]
  have hwW : ∀ i < Q, w i ∈ Wodd := by
    intro i hi
    rcases (by omega : i < Q - 1 ∨ i = Q - 1) with h | h
    · rw [hw_lt i h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_range.2 h))))
    · rw [h, hw_last]; simp [hWodd]
  have hGv : ∀ v ∈ G, v ∈ A ∧ (v % 2 = 1 → v ∈ Wodd) ∧ (v ∈ Estar n → v = e1) := by
    intro v hv
    rcases mem_gpPath hQ1 hv with rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact ⟨hg1A, fun _ => hg1W, fun h => by have := even_of_mem_Estar h; omega⟩
    · exact ⟨he1A, fun h => by have := even_of_mem_Estar he1E; omega, fun _ => rfl⟩
    · exact ⟨hg2A, fun _ => hg2W, fun h => by have := even_of_mem_Estar h; omega⟩
    · exact ⟨(hwprop i hi).1, fun _ => hwW i hi,
        fun h => by have := even_of_mem_Estar h; have := hwodd i hi; omega⟩
    · have := (hyprop i hi).2.1
      exact ⟨(hyprop i hi).1, fun h => by omega,
        fun h => by have := (mem_Estar.1 h).2; omega⟩
  -- the single vertices
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (show l - 1 - Q ≤ (Good A θ \ Wodd).card by
    have := Finset.le_card_sdiff Wodd (Good A θ); omega)
  have hSmem : ∀ c ∈ S, (c ∈ A ∧ c % 2 = 1 ∧ θ ≤ rho c) ∧ c ∉ Wodd := by
    intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 (hS hc)
    exact ⟨mem_Good.1 h1, h2⟩
  have hg1S : g1 ∉ S := fun h => (hSmem g1 h).2 hg1W
  have hGS : ∀ v ∈ G, v ∉ S := fun v hv hvS =>
    (hSmem v hvS).2 ((hGv v hv).2.1 (hSmem v hvS).1.2.1)
  -- the gadgets
  set ex : ℕ → List ℕ := fun c => if c = g1 then G else [c] with hexdef
  have hexg1 : ex g1 = G := by simp [hexdef]
  have hexc : ∀ c, c ≠ g1 → ex c = [c] := fun c hc => by simp [hexdef, hc]
  have hXmem : ∀ c ∈ insert g1 S, c = g1 ∨ (c ∈ S ∧ c ≠ g1) := by
    intro c hc
    rcases Finset.mem_insert.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun h' => hg1S (h' ▸ h)⟩
  set B := ((Estar n).filter (· ∈ A)).erase e1 with hB
  have hBcard : B.card + 1 = ((Estar n).filter (· ∈ A)).card :=
    Finset.card_erase_add_one (Finset.mem_filter.2 ⟨he1E, he1A⟩)
  have hcyc := assembly ex A (insert g1 S) B k
    (by -- nonempty paths
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexg1]; exact gpPath_ne_nil
      · rw [hexc c hcg]; simp)
    (by -- chains
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexg1]
        refine gpPath_chain hQ1 he1c.1.symm he1c.2 (fun i hi => (hyprop i hi).2.2.1.symm)
          (fun i hi => (hyprop i hi).2.2.2) ?_
        rw [hw_last]; exact hcopwg
      · rw [hexc c hcg]; exact List.IsChain.singleton _)
    (by -- no repetition inside a path
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexg1]
        have he6 := he16
        refine gpPath_nodup hQ1 hg1g2 (by omega) (by omega)
          (fun i hi => (hwprop i hi).2.2.2.1.symm)
          (fun i hi => by have := (hyprop i hi).2.1; omega)
          (fun i hi => by have := hwodd i hi; omega)
          (fun i hi => by have := (hyprop i hi).2.1; omega)
          (fun i hi => (hwprop i hi).2.2.2.2.symm)
          (fun i hi => by have := (hyprop i hi).2.1; omega)
          (fun i hi i' hi' => by have := (hyprop i' hi').2.1; have := hwodd i hi; omega)
          hwinj
          (fun i hi i' hi' h => hyinj (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))
            (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) h)
      · rw [hexc c hcg]; exact List.nodup_singleton _)
    (by -- disjoint paths
      intro c hc c' hc' hcc' v hv hv'
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩ <;> rcases hXmem c' hc' with rfl | ⟨hcS', hcg'⟩
      · exact hcc' rfl
      · rw [hexg1] at hv; rw [hexc c' hcg'] at hv'
        rw [List.mem_singleton] at hv'; subst hv'
        exact hGS v hv hcS'
      · rw [hexc c hcg] at hv; rw [hexg1] at hv'
        rw [List.mem_singleton] at hv; subst hv
        exact hGS v hv' hcS
      · rw [hexc c hcg] at hv; rw [hexc c' hcg'] at hv'
        rw [List.mem_singleton] at hv hv'
        exact hcc' (hv.symm.trans hv'))
    (by -- paths avoid the pool
      intro c hc v hv hvB
      obtain ⟨hve, hv'⟩ := Finset.mem_erase.1 hvB
      have hvE := (Finset.mem_filter.1 hv').1
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · rw [hexg1] at hv; exact hve ((hGv v hv).2.2 hvE)
      · rw [hexc c hcg, List.mem_singleton] at hv; subst hv
        have := even_of_mem_Estar hvE
        have := (hSmem v hcS).1.2.1
        omega)
    (by -- paths lie in `A`
      intro c hc v hv
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · rw [hexg1] at hv; exact (hGv v hv).1
      · rw [hexc c hcg, List.mem_singleton] at hv; subst hv
        exact (hSmem v hcS).1.1)
    (fun v hv => (Finset.mem_filter.1 (Finset.mem_erase.1 hv).2).2)
    (by rw [Finset.card_insert_of_notMem hg1S, hScard]; omega)
    (by rw [Finset.card_insert_of_notMem hg1S, hScard]; omega)
    (by omega)
    (by -- degrees
      intro c hc
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · refine (deg_pool_GP (A := A) (e1 := e1) hn hg1I hg2I hg12 hg22 hρG H9).trans
          (Finset.card_le_card ?_)
        intro β hβ
        obtain ⟨hβB, hβ1, hβ2⟩ := Finset.mem_filter.1 hβ
        refine Finset.mem_filter.2 ⟨hβB, ?_⟩
        unfold EndRel
        rw [hexg1, gpPath_head, gpPath_last hQ1]
        exact ⟨hβ1, hβ2⟩
      · obtain ⟨⟨hcA, hc2, hcρ⟩, -⟩ := hSmem c hcS
        refine (deg_pool_GP (A := A) (e1 := e1) hn (hA hcA) (hA hcA) hc2 hc2
          (by rw [Nat.lcm_self]; exact hcρ) H9).trans (Finset.card_le_card ?_)
        intro β hβ
        obtain ⟨hβB, hβ1, hβ2⟩ := Finset.mem_filter.1 hβ
        refine Finset.mem_filter.2 ⟨hβB, ?_⟩
        unfold EndRel
        rw [hexc c hcg]
        exact ⟨hβ1, hβ2⟩)
  have hsum : ∑ c ∈ insert g1 S, (ex c).length = (2 * Q + 2) + S.card := by
    rw [Finset.sum_insert hg1S, hexg1, gpPath_length]
    rw [Finset.sum_congr rfl (fun c hc => by rw [hexc c (fun h => hg1S (h ▸ hc))])]
    simp
  rw [hsum, Finset.card_insert_of_notMem hg1S, hScard] at hcyc
  convert hcyc using 1
  omega

end ErdosSar
