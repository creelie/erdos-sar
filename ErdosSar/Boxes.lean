import ErdosSar.SchemeT
import ErdosSar.Cert
import ErdosSar.Triangle

/-!
# From density certificates to the two constructions

For a set `A ⊆ [1, n]` with `|A| > T(n)` let `d = |E* \ A|`, `μ₆ = |M₆ \ A|` and
`μ_T = |(A \ U)ᶜ ∩ [1, n] \ U| = |Pool23 \ A|`. The lemmas `gp_box` and `t_box` show that, inside a
box of values of `(3d/n, μ₆/n)` or of `μ_T/n` satisfying finitely many rational inequalities, the
hypotheses of `gp_cycle` or `t_cycle` hold.
-/

namespace ErdosSar

open Finset

/-- The certified bound at a fixed `n`. -/
def BadAt (n : ℕ) (θ β : ℝ) : Prop :=
  ∀ R : Finset ℕ, SymRes R → R.Nonempty →
    (((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < θ)).card : ℝ) ≤ n / 6 * R.card * β

theorem badAt_of_badBound {θ β : ℝ} (h : BadBound θ β) : ∃ N, ∀ n ≥ N, BadAt n θ β := h

/-- The odd residues mod `6`. -/
def ROdd : Finset ℕ := {1, 3, 5}

theorem symRes_ROdd : SymRes ROdd := by unfold SymRes ROdd; decide

theorem card_ROdd : ROdd.card = 3 := by decide

theorem bad_mono {n : ℕ} {R : Finset ℕ} {t g : ℝ} (htg : t ≤ g) :
    ((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < t)).card ≤
      ((Icc 1 n).filter (fun z => z % 6 ∈ R ∧ rho z < g)).card :=
  Finset.card_le_card (fun z hz => by
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨h1, h2, lt_of_lt_of_le h3 htg⟩)

theorem card_Good_ge {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) {t g β : ℝ} (htg : t ≤ g)
    (hbad : BadAt n g β) : ((A.filter Odd).card : ℝ) - n / 2 * β ≤ (Good A t).card := by
  have hsub : A.filter Odd ⊆ Good A t ∪
      ((Icc 1 n).filter (fun z => z % 6 ∈ ROdd ∧ rho z < t)) := by
    intro z hz
    obtain ⟨hzA, hzo⟩ := Finset.mem_filter.1 hz
    have hz2 := Nat.odd_iff.1 hzo
    by_cases hρ : t ≤ rho z
    · exact Finset.mem_union_left _ (mem_Good.2 ⟨hzA, hz2, hρ⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hA hzA, ?_, lt_of_not_ge hρ⟩)
      simp only [ROdd, Finset.mem_insert, Finset.mem_singleton]; omega
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := (bad_mono (n := n) (R := ROdd) htg)
  have h3 := hbad ROdd symRes_ROdd (by decide)
  rw [card_ROdd] at h3
  have h12 : ((A.filter Odd).card : ℝ) ≤ (Good A t).card +
      ((Icc 1 n).filter (fun z => z % 6 ∈ ROdd ∧ rho z < g)).card := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  push_cast at h3
  linarith

theorem card_GoodU_ge {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) {t g β : ℝ} (htg : t ≤ g)
    (hbad : BadAt n g β) :
    ((A.filter (fun z => z % 6 ∈ RU)).card : ℝ) - n / 3 * β ≤ (GoodU A t).card := by
  have hsub : A.filter (fun z => z % 6 ∈ RU) ⊆ GoodU A t ∪
      ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t)) := by
    intro z hz
    obtain ⟨hzA, hzu⟩ := Finset.mem_filter.1 hz
    by_cases hρ : t ≤ rho z
    · exact Finset.mem_union_left _ (mem_GoodU.2 ⟨hzA, mem_RU.1 hzu, hρ⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hA hzA, hzu, lt_of_not_ge hρ⟩)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := (bad_mono (n := n) (R := RU) htg)
  have h3 := hbad RU symRes_RU (by decide)
  rw [card_RU] at h3
  have h12 : ((A.filter (fun z => z % 6 ∈ RU)).card : ℝ) ≤ (GoodU A t).card +
      ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < g)).card := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  push_cast at h3
  linarith

theorem bad_RU_le {n : ℕ} {t g β : ℝ} (htg : t ≤ g) (hbad : BadAt n g β) :
    (((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t)).card : ℝ) ≤ n / 3 * β := by
  have h2 : (((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < t)).card : ℝ) ≤
      ((Icc 1 n).filter (fun z => z % 6 ∈ RU ∧ rho z < g)).card := by
    exact_mod_cast bad_mono (n := n) (R := RU) htg
  have h3 := hbad RU symRes_RU (by decide)
  rw [card_RU] at h3
  push_cast at h3
  linarith

theorem card_M6 (n : ℕ) : (M6 n).card = n / 6 := by
  unfold M6
  rw [card_res n 0 6 (by norm_num) le_rfl (by norm_num)]
  omega

theorem card_Estar (n : ℕ) : (Estar n).card = n / 2 - n / 6 := by
  rw [← Cnt_empty_eq_card_Estar, Cnt_empty]

/-- The basic counts for `A ⊆ [1, n]` with `|A| > T(n)`. -/
theorem open_counts {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : T n < A.card) :
    o n + 1 + (Estar n \ A).card + (M6 n \ A).card ≤ (A.filter Odd).card ∧
    (Pool23 n \ A).card + 1 ≤ (A.filter (fun z => z % 6 ∈ RU)).card ∧
    (Estar n \ A).card + (M6 n \ A).card ≤ (Pool23 n \ A).card ∧
    (Units n \ A).card + (A.filter (fun z => z % 6 ∈ RU)).card + T n = n ∧
    (Pool23 n \ A).card ≤ T n := by
  classical
  -- odd elements
  have hD : (Estar n \ A) ∪ (M6 n \ A) ⊆ (Icc 1 n).filter Even := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨hzE, -⟩ := Finset.mem_sdiff.1 h
      obtain ⟨hzI, hz6⟩ := mem_Estar.1 hzE
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hzI, Nat.even_iff.2 (by omega)⟩
    · obtain ⟨hzM, -⟩ := Finset.mem_sdiff.1 h
      obtain ⟨hzI, hz6⟩ := mem_M6.1 hzM
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hzI, Nat.even_iff.2 (by omega)⟩
  have hDA : Disjoint ((Estar n \ A) ∪ (M6 n \ A)) A := by
    rw [Finset.disjoint_left]
    intro z hz hzA
    rcases Finset.mem_union.1 hz with h | h
    · exact (Finset.mem_sdiff.1 h).2 hzA
    · exact (Finset.mem_sdiff.1 h).2 hzA
  have hEM : Disjoint (Estar n \ A) (M6 n \ A) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have h1 := (mem_Estar.1 (Finset.mem_sdiff.1 hz).1).2
    have h2 := (mem_M6.1 (Finset.mem_sdiff.1 hz').1).2
    omega
  have hodd := card_odd_ge hA hcard _ hD hDA
  rw [Finset.card_union_of_disjoint hEM] at hodd
  -- units
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun z => z % 6 ∈ RU)
  have hPA : (Pool23 n).filter (· ∈ A) ∪ (Pool23 n \ A) = Pool23 n := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]; tauto
  have hPAd : Disjoint ((Pool23 n).filter (· ∈ A)) (Pool23 n \ A) := by
    rw [Finset.disjoint_left]; intro z hz hz'
    exact (Finset.mem_sdiff.1 hz').2 (Finset.mem_filter.1 hz).2
  have hPcard : ((Pool23 n).filter (· ∈ A)).card + (Pool23 n \ A).card = T n := by
    rw [← Finset.card_union_of_disjoint hPAd, hPA, card_Pool23]
  have hnotU : A.filter (fun z => ¬ z % 6 ∈ RU) ⊆ (Pool23 n).filter (· ∈ A) := by
    intro z hz
    obtain ⟨hzA, hzu⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hA hzA, mem_R23.2 (fun h => hzu
      (mem_RU.2 h))⟩, hzA⟩
  have h1 := Finset.card_le_card hnotU
  -- the subsets of missing elements
  have hsubP : (Estar n \ A) ∪ (M6 n \ A) ⊆ Pool23 n \ A := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨hzE, hzA⟩ := Finset.mem_sdiff.1 h
      obtain ⟨hzI, hz6⟩ := mem_Estar.1 hzE
      refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hzI, ?_⟩, hzA⟩
      rw [mem_R23]; omega
    · obtain ⟨hzM, hzA⟩ := Finset.mem_sdiff.1 h
      obtain ⟨hzI, hz6⟩ := mem_M6.1 hzM
      refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hzI, ?_⟩, hzA⟩
      rw [mem_R23]; omega
  have h2 := Finset.card_le_card hsubP
  rw [Finset.card_union_of_disjoint hEM] at h2
  -- units missing from `A`
  have hUA : (Units n).filter (· ∈ A) = A.filter (fun z => z % 6 ∈ RU) := by
    ext z
    simp only [Units, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, h⟩, hzA⟩; exact ⟨hzA, h⟩
    · rintro ⟨hzA, h⟩; exact ⟨⟨hA hzA, h⟩, hzA⟩
  have hU := Finset.card_filter_add_card_filter_not (s := Units n) (fun z => z ∈ A)
  have e : (Units n).filter (fun z => z ∉ A) = Units n \ A := by ext; simp
  rw [e, hUA] at hU
  have hUn := card_Units n
  refine ⟨by omega, by omega, h2, by omega, by omega⟩

/-- **Boxes for the giant-path construction.** -/
theorem gp_box {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : T n < A.card)
    {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (d0 d1 a0 a1 s t1 θ θw sw κ gs gt1 gθ gθw βs βt1 βθ βθw : ℚ)
    (hd0 : (d0 : ℝ) * n ≤ 3 * (Estar n \ A).card)
    (hd1 : 3 * ((Estar n \ A).card : ℝ) ≤ d1 * n)
    (ha0 : (a0 : ℝ) * n ≤ (M6 n \ A).card) (ha1 : ((M6 n \ A).card : ℝ) ≤ a1 * n)
    (bs : BadAt n gs βs) (bt1 : BadAt n gt1 βt1) (bθ : BadAt n gθ βθ) (bθw : BadAt n gθw βθw)
    (cs : s ≤ gs) (ct1 : t1 ≤ gt1) (cθ : θ ≤ gθ) (cθw : θw ≤ gθw)
    (c0 : 0 ≤ t1) (c1 : 0 ≤ θw) (c2 : 0 ≤ κ) (csw : sw ≤ s) (D1 : d1 ≤ 9 / 10)
    (B1 : 1 / 2 + d1 / 2 + 3 * κ + 5 / 10 ^ 4 ≤ θ)
    (BP : βs / 2 + 5 / 10 ^ 4 ≤ d0 / 3 + a0)
    (BG : βt1 / 2 + 5 / 10 ^ 4 ≤ 1 / 6 + d0 / 3 + a0)
    (BH : θ ≤ t1 * s)
    (BE : d1 + 5 / 10 ^ 4 ≤ t1 * sw)
    (BS : βθ / 2 + 5 / 10 ^ 4 ≤ d0 / 3 + a0)
    (BWY : κ < d1 / 6 + 5 / 10 ^ 4 → βθw / 3 + 5 / 10 ^ 4 ≤ d0 / 6 + a0 + κ ∧
      d1 / 6 - κ + a1 + 5 / 10 ^ 4 ≤ θw * sw / 6 ∧ sw ≤ θw) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨hodd, -, -, -, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set E := (Estar n).card with hE
  have hEc : E = n / 2 - n / 6 := card_Estar n
  have hdE : d ≤ E := Finset.card_le_card Finset.sdiff_subset
  have hnR := n_ge_of_N₁ hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- real forms of the box inequalities
  have cs' : (s : ℝ) ≤ gs := Rat.cast_le.2 cs
  have ct1' : (t1 : ℝ) ≤ gt1 := Rat.cast_le.2 ct1
  have cθ' : (θ : ℝ) ≤ gθ := Rat.cast_le.2 cθ
  have cθw' : (θw : ℝ) ≤ gθw := Rat.cast_le.2 cθw
  have c0' : ((0 : ℚ) : ℝ) ≤ t1 := Rat.cast_le.2 c0
  have c1' : ((0 : ℚ) : ℝ) ≤ θw := Rat.cast_le.2 c1
  have c2' : ((0 : ℚ) : ℝ) ≤ κ := Rat.cast_le.2 c2
  have csw' : (sw : ℝ) ≤ s := Rat.cast_le.2 csw
  have D1' : (d1 : ℝ) ≤ ((9 / 10 : ℚ) : ℝ) := Rat.cast_le.2 D1
  have B1' : ((1 / 2 + d1 / 2 + 3 * κ + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ θ := Rat.cast_le.2 B1
  have BP' : ((βs / 2 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((d0 / 3 + a0 : ℚ) : ℝ) := Rat.cast_le.2 BP
  have BG' : ((βt1 / 2 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((1 / 6 + d0 / 3 + a0 : ℚ) : ℝ) :=
    Rat.cast_le.2 BG
  have BH' : (θ : ℝ) ≤ ((t1 * s : ℚ) : ℝ) := Rat.cast_le.2 BH
  have BE' : ((d1 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((t1 * sw : ℚ) : ℝ) := Rat.cast_le.2 BE
  have BS' : ((βθ / 2 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((d0 / 3 + a0 : ℚ) : ℝ) := Rat.cast_le.2 BS
  push_cast at c0' c1' c2' D1' B1' BP' BG' BH' BE' BS'
  -- the counts
  have hoddR : (o n : ℝ) + 1 + d + μ6 ≤ (A.filter Odd).card := by exact_mod_cast hodd
  have hon : (n : ℝ) ≤ 6 * o n + 6 := by
    have : n ≤ 6 * o n + 6 := by unfold o; omega
    exact_mod_cast this
  have hlo : l ≤ o n := by unfold o; omega
  have hloR : (l : ℝ) ≤ o n := by exact_mod_cast hlo
  have hlR : (6 : ℝ) * l ≤ n := by exact_mod_cast hl
  have hER1 : (3 : ℝ) * E ≤ n + 3 := by
    have : 3 * E ≤ n + 3 := by rw [hEc]; omega
    exact_mod_cast this
  have hER2 : (n : ℝ) ≤ 3 * E + 3 := by
    have : n ≤ 3 * E + 3 := by rw [hEc]; omega
    exact_mod_cast this
  have hdm0 : (d0 : ℝ) * n / 3 + a0 * n ≤ d + μ6 := by linarith
  have hdR : (3 : ℝ) * d ≤ d1 * n := hd1
  have hd1n : (d1 : ℝ) * n ≤ 9 / 10 * n := mul_le_mul_of_nonneg_right D1' hn0
  -- the parameter `k`
  obtain ⟨K, hK⟩ : ∃ K, K = ⌊(κ : ℝ) * n⌋₊ := ⟨_, rfl⟩
  have hK1 : (K : ℝ) ≤ κ * n := by rw [hK]; exact Nat.floor_le (by positivity)
  have hK2 : (κ : ℝ) * n < K + 1 := by rw [hK]; exact Nat.lt_floor_add_one _
  obtain ⟨k, hk⟩ : ∃ k, k = (E - d + 2) / 2 + K := ⟨_, rfl⟩
  have hk1 : E + 1 + 2 * K ≤ 2 * k + d := by omega
  have hk1R : (E : ℝ) + 1 + 2 * K ≤ 2 * k + d := by exact_mod_cast hk1
  have hk2R : (2 : ℝ) * k + d ≤ E + 2 + 2 * K := by
    have : 2 * k + d ≤ E + 2 + 2 * K := by omega
    exact_mod_cast this
  -- `k ≥ l` unless `κ` is small
  have hkl : k < l → κ < d1 / 6 + 5 / 10 ^ 4 := by
    intro hlt
    by_contra hcon
    push Not at hcon
    have hcon' : ((d1 / 6 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ κ := Rat.cast_le.2 hcon
    push_cast at hcon'
    have hlt' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hlt
    have := mul_le_mul_of_nonneg_right hcon' hn0
    linarith
  -- the hypotheses of the construction
  have hGs := card_Good_ge hA cs' bs
  have hGt1 := card_Good_ge hA ct1' bt1
  have hGθ := card_Good_ge hA cθ' bθ
  have hGUθw := card_GoodU_ge (A := A) hA cθw' bθw
  refine gp_cycle (s := s) (t1 := t1) (θ := θ) (θw := θw) (sw := sw) (k := k) hn hA hl2 ?_
    c0' c1' csw' ?_ ?_ ?_ BH' ?_ ?_ ?_ ?_ ?_ ?_
  · -- `2 ≤ k`
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  · -- `sw ≤ θw` when `k < l`
    intro hlt
    exact Rat.cast_le.2 (BWY (hkl hlt)).2.2
  · -- `H1`
    have h := mul_le_mul_of_nonneg_right BP' hn0
    have : ((o n + 1 : ℕ) : ℝ) ≤ (Good A s).card := by push_cast; linarith
    exact_mod_cast this
  · -- `H2`
    have h := mul_le_mul_of_nonneg_right BG' hn0
    have : ((3 : ℕ) : ℝ) ≤ (Good A t1).card := by push_cast; linarith
    exact_mod_cast this
  · -- `H4`
    intro hlt
    obtain ⟨W1, -, -⟩ := BWY (hkl hlt)
    have W1' : ((βθw / 3 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((d0 / 6 + a0 + κ : ℚ) : ℝ) := Rat.cast_le.2 W1
    push_cast at W1'
    have h := mul_le_mul_of_nonneg_right W1' hn0
    obtain ⟨-, hu, hdμ, -, -⟩ := open_counts hA hcard
    have huR : ((Pool23 n \ A).card : ℝ) + 1 ≤ (A.filter (fun z => z % 6 ∈ RU)).card := by
      exact_mod_cast hu
    have hdμR : (d : ℝ) + μ6 ≤ (Pool23 n \ A).card := by exact_mod_cast hdμ
    have hsub : ((l - k + 2 : ℕ) : ℝ) = l - k + 2 := by
      rw [Nat.cast_add, Nat.cast_sub hlt.le]; push_cast; ring
    have : ((l - k + 2 : ℕ) : ℝ) ≤ (GoodU A θw).card := by rw [hsub]; linarith
    exact_mod_cast this
  · -- `H5`
    have h := mul_le_mul_of_nonneg_left BE' (by positivity : (0 : ℝ) ≤ n / 3)
    linarith
  · -- `H6`
    intro hlt
    obtain ⟨-, Y1, -⟩ := BWY (hkl hlt)
    have Y1' : ((d1 / 6 - κ + a1 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ ((θw * sw / 6 : ℚ) : ℝ) :=
      Rat.cast_le.2 Y1
    push_cast at Y1'
    have hsub : ((l - k - 1 : ℕ) : ℝ) = l - k - 1 := by
      have : l - k - 1 + k + 1 = l := by omega
      have h' : ((l - k - 1 : ℕ) : ℝ) + k + 1 = l := by exact_mod_cast this
      linarith
    rw [hsub]
    have h := mul_le_mul_of_nonneg_right Y1' hn0
    linarith
  · -- `H7`
    have h := mul_le_mul_of_nonneg_right BS' hn0
    have : ((l + 1 : ℕ) : ℝ) ≤ (Good A θ).card := by push_cast; linarith
    exact_mod_cast this
  · -- `H8`
    omega
  · -- `H9`
    have h := mul_le_mul_of_nonneg_left B1' (by positivity : (0 : ℝ) ≤ n / 3)
    linarith

/-- **Boxes for the unit construction.** -/
theorem t_box {n : ℕ} (hn : N₁ ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : T n < A.card)
    {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (lam0 lam1 θT r1 t2 gθT gr1 gt2 βθT βr1 βt2 : ℚ)
    (hlam0 : (lam0 : ℝ) * n ≤ (Pool23 n \ A).card)
    (hlam1 : ((Pool23 n \ A).card : ℝ) ≤ lam1 * n + 1)
    (bθT : BadAt n gθT βθT) (br1 : BadAt n gr1 βr1) (bt2 : BadAt n gt2 βt2)
    (cθT : θT ≤ gθT) (cr1 : r1 ≤ gr1) (ct2 : t2 ≤ gt2) (c0 : 0 ≤ r1)
    (C1 : 1 / 2 + 3 * lam1 / 4 + 5 / 10 ^ 4 ≤ θT)
    (C2 : 1 / 6 + βθT / 3 + 5 / 10 ^ 4 ≤ lam0)
    (C3 : βr1 / 3 + 5 / 10 ^ 4 ≤ lam0)
    (C4 : βt2 / 3 + (1 - r1) / 3 + 5 / 10 ^ 4 ≤ lam0)
    (C5 : θT ≤ r1 * t2) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, -, hUn, hμT⟩ := open_counts hA hcard
  set μT := (Pool23 n \ A).card with hμTdef
  set u := (A.filter (fun z => z % 6 ∈ RU)).card with hudef
  have hnR := n_ge_of_N₁ hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have cθT' : (θT : ℝ) ≤ gθT := Rat.cast_le.2 cθT
  have cr1' : (r1 : ℝ) ≤ gr1 := Rat.cast_le.2 cr1
  have ct2' : (t2 : ℝ) ≤ gt2 := Rat.cast_le.2 ct2
  have c0' : ((0 : ℚ) : ℝ) ≤ r1 := Rat.cast_le.2 c0
  have C1' : ((1 / 2 + 3 * lam1 / 4 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ θT := Rat.cast_le.2 C1
  have C2' : ((1 / 6 + βθT / 3 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ lam0 := Rat.cast_le.2 C2
  have C3' : ((βr1 / 3 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ lam0 := Rat.cast_le.2 C3
  have C4' : ((βt2 / 3 + (1 - r1) / 3 + 5 / 10 ^ 4 : ℚ) : ℝ) ≤ lam0 := Rat.cast_le.2 C4
  have C5' : (θT : ℝ) ≤ ((r1 * t2 : ℚ) : ℝ) := Rat.cast_le.2 C5
  push_cast at c0' C1' C2' C3' C4' C5'
  have huR : (μT : ℝ) + 1 ≤ u := by exact_mod_cast hu
  have hlR : (6 : ℝ) * l ≤ n := by exact_mod_cast hl
  obtain ⟨k, hk⟩ : ∃ k, k = (T n - μT + 3) / 2 := ⟨_, rfl⟩
  have hTn : T n = n / 2 + n / 3 - n / 6 := rfl
  have hlk : l ≤ k := by omega
  have hkR : (2 : ℝ) * k + μT ≤ T n + 3 := by
    have : 2 * k + μT ≤ T n + 3 := by omega
    exact_mod_cast this
  have hTR : (3 : ℝ) * T n ≤ 2 * n + 3 := by
    have : 3 * T n ≤ 2 * n + 3 := by omega
    exact_mod_cast this
  have hUR : (3 : ℝ) * ((Units n \ A).card + u) ≤ n + 3 := by
    have : 3 * ((Units n \ A).card + u) ≤ n + 3 := by omega
    exact_mod_cast this
  have hGθT := card_GoodU_ge (A := A) hA cθT' bθT
  have hGr1 := card_GoodU_ge (A := A) hA cr1' br1
  have hbt2 := bad_RU_le (n := n) ct2' bt2
  refine t_cycle (θT := θT) (r1 := r1) (t2 := t2) (k := k) hn hA hl2 hlk c0' C5' ?_ ?_ ?_ ?_ ?_
  · -- `T1`
    have h := mul_le_mul_of_nonneg_right C2' hn0
    have : ((l + 1 : ℕ) : ℝ) ≤ (GoodU A θT).card := by push_cast; linarith
    exact_mod_cast this
  · -- `T2`
    have h := mul_le_mul_of_nonneg_right C3' hn0
    have : (1 : ℝ) ≤ (GoodU A r1).card := by linarith
    have : 1 ≤ (GoodU A r1).card := by exact_mod_cast this
    exact Finset.card_pos.1 (by omega)
  · -- `T3`
    have h := mul_le_mul_of_nonneg_right C4' hn0
    linarith
  · -- `T5`
    have h := mul_le_mul_of_nonneg_left C1' (by positivity : (0 : ℝ) ≤ 2 * n / 3)
    linarith
  · -- `T6`
    rw [card_Pool23]; omega

end ErdosSar
