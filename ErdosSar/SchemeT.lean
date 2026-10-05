import ErdosSar.SchemeGP
import ErdosSar.Extremal

/-!
# The construction with pool `A \ U`

When many multiples of `2` or `3` are missing from `A`, the units of `A` are numerous. We use
`l - 1` single units of large density and one path `w, w'` of two coprime units, and close them
into a cycle of length `2l + 1` through the pool of all multiples of `2` or `3` that lie in `A`.
-/

namespace ErdosSar

open Finset

/-- The residues mod `6` of the multiples of `2` or `3`. -/
def R23 : Finset ℕ := {0, 2, 3, 4}

/-- The residues mod `6` of the units. -/
def RU : Finset ℕ := {1, 5}

theorem symRes_R23 : SymRes R23 := by unfold SymRes R23; decide

theorem symRes_RU : SymRes RU := by unfold SymRes RU; decide

theorem card_R23 : R23.card = 4 := by decide

theorem card_RU : RU.card = 2 := by decide

/-- The multiples of `2` or `3` in `[1, n]`. -/
def Pool23 (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun z => z % 6 ∈ R23)

/-- The units in `[1, n]`. -/
def Units (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun z => z % 6 ∈ RU)

theorem mem_R23 {z : ℕ} : z % 6 ∈ R23 ↔ ¬ (z % 6 = 1 ∨ z % 6 = 5) := by
  simp only [R23, Finset.mem_insert, Finset.mem_singleton]; omega

theorem mem_RU {z : ℕ} : z % 6 ∈ RU ↔ (z % 6 = 1 ∨ z % 6 = 5) := by
  simp [RU]

theorem card_Pool23 (n : ℕ) : (Pool23 n).card = T n := by
  rw [← card_M23]
  congr 1
  apply Finset.filter_congr
  intro z _
  rw [mem_R23]
  omega

theorem card_Units (n : ℕ) : (Units n).card + T n = n := by
  rw [← card_Pool23]
  have h := Finset.card_filter_add_card_filter_not (s := Icc 1 n) (fun z => z % 6 ∈ RU)
  have e : (Icc 1 n).filter (fun z => ¬ z % 6 ∈ RU) = Pool23 n := by
    unfold Pool23
    apply Finset.filter_congr
    intro z _
    rw [mem_R23, mem_RU]
  rw [e, Nat.card_Icc] at h
  unfold Units
  omega

/-- Degree of a gadget with unit ends `p, q` into the pool `(A \ U) = Pool23 ∩ A`. -/
theorem deg_pool_T {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} {p q : ℕ} (hp : p ∈ Icc 1 n)
    (hq : q ∈ Icc 1 n) (hpu : p % 6 = 1 ∨ p % 6 = 5) (hqu : q % 6 = 1 ∨ q % 6 = 5) {θ : ℝ}
    (hρ : θ ≤ rho (Nat.lcm p q)) {k : ℕ}
    (T5 : (k : ℝ) + (Pool23 n \ A).card + 4 * (n / 10 ^ 6) ≤ 2 * n / 3 * θ) :
    k ≤ (((Pool23 n).filter (· ∈ A)).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card := by
  set m := Nat.lcm p q with hm
  have hm0 : m ≠ 0 := lcm_ne_zero' hp hq
  have hu := lcm_unit hpu hqu
  have hcnt := card_class_coprime_ge_big (n := n) (R := R23) symRes_R23 hn hm0 (lcm_le_sq hp hq)
    (fun h => absurd h hu.1) (fun h => absurd h hu.2)
  rw [card_R23] at hcnt
  have hsub : ((Icc 1 n).filter (fun z => z % 6 ∈ R23 ∧ Nat.Coprime z m)) ⊆
      (((Pool23 n).filter (· ∈ A)).filter (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)) ∪
        (Pool23 n \ A) := by
    intro z hz
    obtain ⟨hzI, hz6, hzc⟩ := Finset.mem_filter.1 hz
    have hzP : z ∈ Pool23 n := Finset.mem_filter.2 ⟨hzI, hz6⟩
    have hc1 : Nat.Coprime z p := Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_left p q) hzc
    have hc2 : Nat.Coprime z q := Nat.Coprime.coprime_dvd_right (Nat.dvd_lcm_right p q) hzc
    by_cases hzA : z ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzP, hzA⟩,
        hc2.symm, hc1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hzP, hzA⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (((Pool23 n).filter (· ∈ A)).filter
    (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)) (Pool23 n \ A)
  have h12 : (((Icc 1 n).filter (fun z => z % 6 ∈ R23 ∧ Nat.Coprime z m)).card : ℝ) ≤
      ((((Pool23 n).filter (· ∈ A)).filter
        (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card : ℝ) + (Pool23 n \ A).card := by
    exact_mod_cast h1.trans h2
  have h3 : (n : ℝ) / 6 * 4 * θ ≤ (n : ℝ) / 6 * 4 * rho m :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  push_cast at hcnt
  have : (k : ℝ) ≤ ((((Pool23 n).filter (· ∈ A)).filter
      (fun β => Nat.Coprime q β ∧ Nat.Coprime β p)).card : ℝ) := by linarith
  exact_mod_cast this

/-- **The unit construction.** -/
theorem t_cycle {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    {l k : ℕ} (hl2 : 2 ≤ l) (hlk : l ≤ k) {θT r1 t2 : ℝ} (hr0 : 0 ≤ r1) (T4 : θT ≤ r1 * t2)
    (T1 : l + 1 ≤ (GoodU A θT).card) (T2 : (GoodU A r1).Nonempty)
    (T3 : (2 : ℝ) + 2 * (n / 10 ^ 6) + (Units n \ A).card +
      ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t2)).card ≤ n / 3 * r1)
    (T5 : (k : ℝ) + (Pool23 n \ A).card + 4 * (n / 10 ^ 6) ≤ 2 * n / 3 * θT)
    (T6 : (Pool23 n).card + 2 ≤ 2 * k + (Pool23 n \ A).card) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  classical
  have hI0 : ∀ z ∈ Icc 1 n, z ≠ 0 := fun z hz => by have := (Finset.mem_Icc.1 hz).1; omega
  obtain ⟨w, hw⟩ := T2
  obtain ⟨hwA, hwu, hwρ⟩ := mem_GoodU.1 hw
  have hwI := hA hwA
  -- the partner `w'`
  obtain ⟨w', hw'⟩ : ∃ w', w' ∈ ((GoodU A t2).filter (fun z => Nat.Coprime z w)).erase w := by
    have hn2 : w ≤ n ^ 2 := by
      have := (Finset.mem_Icc.1 hwI).2
      nlinarith
    have hcnt := card_class_coprime_ge_big (n := n) (R := RU) symRes_RU hn (hI0 _ hwI) hn2
      (fun h => by rcases hwu with h' | h' <;> omega)
      (fun h => by rcases hwu with h' | h' <;> omega)
    rw [card_RU] at hcnt
    push_cast at hcnt
    have hsub : ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ Nat.Coprime z w)) ⊆
        ((GoodU A t2).filter (fun z => Nat.Coprime z w)) ∪ (Units n \ A) ∪
          ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t2)) := by
      intro z hz
      obtain ⟨hzI, hz6, hzc⟩ := Finset.mem_filter.1 hz
      by_cases hzA : z ∈ A
      · by_cases hzρ : t2 ≤ rho z
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2
            ⟨mem_GoodU.2 ⟨hzA, mem_RU.1 hz6, hzρ⟩, hzc⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzI, hz6, lt_of_not_ge hzρ⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hzI, hz6⟩, hzA⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (((GoodU A t2).filter (fun z => Nat.Coprime z w)) ∪
      (Units n \ A)) ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t2))
    have h3 := Finset.card_union_le ((GoodU A t2).filter (fun z => Nat.Coprime z w))
      (Units n \ A)
    have h4 := Finset.pred_card_le_card_erase (s := (GoodU A t2).filter (fun z => Nat.Coprime z w))
      (a := w)
    have h5 : (n : ℝ) / 6 * 2 * r1 ≤ (n : ℝ) / 6 * 2 * rho w :=
      mul_le_mul_of_nonneg_left hwρ (by positivity)
    have h123 : (((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ Nat.Coprime z w)).card : ℝ) ≤
        (((GoodU A t2).filter (fun z => Nat.Coprime z w)).card : ℝ) + (Units n \ A).card +
          ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t2)).card := by
      exact_mod_cast (h1.trans (h2.trans (Nat.add_le_add_right h3 _)))
    have h6 : (2 : ℝ) ≤ (((GoodU A t2).filter (fun z => Nat.Coprime z w)).card : ℝ) := by
      linarith
    have h7 : 2 ≤ ((GoodU A t2).filter (fun z => Nat.Coprime z w)).card := by exact_mod_cast h6
    exact Finset.card_pos.1 (by omega)
  obtain ⟨hw'w, hw'f⟩ := Finset.mem_erase.1 hw'
  obtain ⟨hw'G, hw'c⟩ := Finset.mem_filter.1 hw'f
  obtain ⟨hw'A, hw'u, hw'ρ⟩ := mem_GoodU.1 hw'G
  have hw'I := hA hw'A
  -- the single units
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq
    (show l - 1 ≤ (GoodU A θT \ {w, w'}).card by
      have h := Finset.le_card_sdiff ({w, w'} : Finset ℕ) (GoodU A θT)
      have h2 : ({w, w'} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      omega)
  have hSmem : ∀ c ∈ S, (c ∈ A ∧ (c % 6 = 1 ∨ c % 6 = 5) ∧ θT ≤ rho c) ∧ c ≠ w ∧ c ≠ w' := by
    intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 (hS hc)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact ⟨mem_GoodU.1 h1, h2⟩
  have hwS : w ∉ S := fun h => (hSmem w h).2.1 rfl
  set ex : ℕ → List ℕ := fun c => if c = w then [w, w'] else [c] with hexdef
  have hexw : ex w = [w, w'] := by simp [hexdef]
  have hexc : ∀ c, c ≠ w → ex c = [c] := fun c hc => by simp [hexdef, hc]
  have hXmem : ∀ c ∈ insert w S, c = w ∨ (c ∈ S ∧ c ≠ w) := by
    intro c hc
    rcases Finset.mem_insert.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun h' => hwS (h' ▸ h)⟩
  have hnotpool : ∀ v, (v % 6 = 1 ∨ v % 6 = 5) → v ∉ Pool23 n := fun v hv hvP =>
    mem_R23.1 (Finset.mem_filter.1 hvP).2 hv
  set B := (Pool23 n).filter (· ∈ A) with hB
  have hBcard : B.card + (Pool23 n \ A).card = (Pool23 n).card := by
    have h := Finset.card_filter_add_card_filter_not (s := Pool23 n) (fun w => w ∈ A)
    have e : (Pool23 n).filter (fun w => w ∉ A) = Pool23 n \ A := by ext; simp
    rw [e] at h; exact h
  have hρww : θT ≤ rho (Nat.lcm w w') := by
    have := rho_lcm_ge_of (hI0 _ hwI) (hI0 _ hw'I) hr0 hwρ hw'ρ
    linarith
  have hcyc := assembly ex A (insert w S) B k
    (by
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexw]; simp
      · rw [hexc c hcg]; simp)
    (by
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexw]
        simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
        exact hw'c.symm
      · rw [hexc c hcg]; exact List.IsChain.singleton _)
    (by
      intro c hc
      rcases hXmem c hc with rfl | ⟨-, hcg⟩
      · rw [hexw]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
          not_false_eq_true, and_true]
        exact fun h => hw'w h.symm
      · rw [hexc c hcg]; exact List.nodup_singleton _)
    (by
      intro c hc c' hc' hcc' v hv hv'
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩ <;> rcases hXmem c' hc' with rfl | ⟨hcS', hcg'⟩
      · exact hcc' rfl
      · rw [hexw] at hv; rw [hexc c' hcg', List.mem_singleton] at hv'; subst hv'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with h | h
        · exact (hSmem v hcS').2.1 h
        · exact (hSmem v hcS').2.2 h
      · rw [hexc c hcg, List.mem_singleton] at hv; rw [hexw] at hv'; subst hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
        rcases hv' with h | h
        · exact (hSmem v hcS).2.1 h
        · exact (hSmem v hcS).2.2 h
      · rw [hexc c hcg, List.mem_singleton] at hv; rw [hexc c' hcg', List.mem_singleton] at hv'
        exact hcc' (hv.symm.trans hv'))
    (by
      intro c hc v hv hvB
      have hvP := (Finset.mem_filter.1 hvB).1
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · rw [hexw] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hnotpool _ hwu hvP
        · exact hnotpool _ hw'u hvP
      · rw [hexc c hcg, List.mem_singleton] at hv; subst hv
        exact hnotpool _ (hSmem v hcS).1.2.1 hvP)
    (by
      intro c hc v hv
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · rw [hexw] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hwA
        · exact hw'A
      · rw [hexc c hcg, List.mem_singleton] at hv; subst hv
        exact (hSmem v hcS).1.1)
    (fun v hv => (Finset.mem_filter.1 hv).2)
    (by rw [Finset.card_insert_of_notMem hwS, hScard]; omega)
    (by rw [Finset.card_insert_of_notMem hwS, hScard]; omega)
    (by omega)
    (by
      intro c hc
      rcases hXmem c hc with rfl | ⟨hcS, hcg⟩
      · refine (deg_pool_T (A := A) hn hwI hw'I hwu hw'u hρww T5).trans (Finset.card_le_card ?_)
        intro β hβ
        obtain ⟨hβB, hβ1, hβ2⟩ := Finset.mem_filter.1 hβ
        refine Finset.mem_filter.2 ⟨hβB, ?_⟩
        unfold EndRel
        rw [hexw]
        exact ⟨hβ1, hβ2⟩
      · obtain ⟨⟨hcA, hcu, hcρ⟩, -⟩ := hSmem c hcS
        refine (deg_pool_T (A := A) hn (hA hcA) (hA hcA) hcu hcu
          (by rw [Nat.lcm_self]; exact hcρ) T5).trans (Finset.card_le_card ?_)
        intro β hβ
        obtain ⟨hβB, hβ1, hβ2⟩ := Finset.mem_filter.1 hβ
        refine Finset.mem_filter.2 ⟨hβB, ?_⟩
        unfold EndRel
        rw [hexc c hcg]
        exact ⟨hβ1, hβ2⟩)
  have hsum : ∑ c ∈ insert w S, (ex c).length = 2 + S.card := by
    rw [Finset.sum_insert hwS, hexw]
    rw [Finset.sum_congr rfl (fun c hc => by rw [hexc c (fun h => hwS (h ▸ hc))])]
    simp
  rw [hsum, Finset.card_insert_of_notMem hwS, hScard] at hcyc
  convert hcyc using 1
  omega

end ErdosSar
