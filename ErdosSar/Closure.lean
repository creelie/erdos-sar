import ErdosSar.Boxes
import ErdosSar.Certs
import ErdosSar.Main

/-!
# Erdős Problem #883, Question 1

The case `70 |E* \ A| ≤ n` is paper Theorem 1.1 (`question1_restricted`). In the remaining case
the proportion `μ_T/n` of multiples of `2` or `3` missing from `A` decides the construction: the
unit construction (`t_box`) when `μ_T ≥ 9n/50`, and the giant-path construction (`gp_box`)
otherwise, on a finite cover of the possible values of `(3d/n, μ₆/n)` by boxes. Each box uses the
density certificates of `Certs.lean` at its thresholds. The case split below is generated from
`verification/open_case/boxes.json` by `verification/open_case/gen_closure.py`.
-/

namespace ErdosSar

open Finset

/-- The certified bounds at the sixteen thresholds, for one `n`. -/
structure Bads (n : ℕ) : Prop where
  b550 : BadAt n ((11 / 20 : ℚ) : ℝ) ((3 / 10000 : ℚ) : ℝ)
  b600 : BadAt n ((3 / 5 : ℚ) : ℝ) ((7 / 2000 : ℚ) : ℝ)
  b625 : BadAt n ((5 / 8 : ℚ) : ℝ) ((1 / 125 : ℚ) : ℝ)
  b650 : BadAt n ((13 / 20 : ℚ) : ℝ) ((89 / 5000 : ℚ) : ℝ)
  b675 : BadAt n ((27 / 40 : ℚ) : ℝ) ((353 / 10000 : ℚ) : ℝ)
  b700 : BadAt n ((7 / 10 : ℚ) : ℝ) ((251 / 5000 : ℚ) : ℝ)
  b725 : BadAt n ((29 / 40 : ℚ) : ℝ) ((93 / 1250 : ℚ) : ℝ)
  b750 : BadAt n ((3 / 4 : ℚ) : ℝ) ((143 / 1250 : ℚ) : ℝ)
  b775 : BadAt n ((31 / 40 : ℚ) : ℝ) ((1049 / 5000 : ℚ) : ℝ)
  b800 : BadAt n ((4 / 5 : ℚ) : ℝ) ((2483 / 10000 : ℚ) : ℝ)
  b825 : BadAt n ((33 / 40 : ℚ) : ℝ) ((1517 / 5000 : ℚ) : ℝ)
  b850 : BadAt n ((17 / 20 : ℚ) : ℝ) ((3457 / 10000 : ℚ) : ℝ)
  b875 : BadAt n ((7 / 8 : ℚ) : ℝ) ((3939 / 10000 : ℚ) : ℝ)
  b900 : BadAt n ((9 / 10 : ℚ) : ℝ) ((4637 / 10000 : ℚ) : ℝ)
  b925 : BadAt n ((37 / 40 : ℚ) : ℝ) ((5387 / 10000 : ℚ) : ℝ)
  b950 : BadAt n ((19 / 20 : ℚ) : ℝ) ((7107 / 10000 : ℚ) : ℝ)

theorem bads_eventually : ∃ N, ∀ n ≥ N, Bads n := by
  obtain ⟨N0, h0⟩ := badAt_of_badBound bad_550
  obtain ⟨N1, h1⟩ := badAt_of_badBound bad_600
  obtain ⟨N2, h2⟩ := badAt_of_badBound bad_625
  obtain ⟨N3, h3⟩ := badAt_of_badBound bad_650
  obtain ⟨N4, h4⟩ := badAt_of_badBound bad_675
  obtain ⟨N5, h5⟩ := badAt_of_badBound bad_700
  obtain ⟨N6, h6⟩ := badAt_of_badBound bad_725
  obtain ⟨N7, h7⟩ := badAt_of_badBound bad_750
  obtain ⟨N8, h8⟩ := badAt_of_badBound bad_775
  obtain ⟨N9, h9⟩ := badAt_of_badBound bad_800
  obtain ⟨N10, h10⟩ := badAt_of_badBound bad_825
  obtain ⟨N11, h11⟩ := badAt_of_badBound bad_850
  obtain ⟨N12, h12⟩ := badAt_of_badBound bad_875
  obtain ⟨N13, h13⟩ := badAt_of_badBound bad_900
  obtain ⟨N14, h14⟩ := badAt_of_badBound bad_925
  obtain ⟨N15, h15⟩ := badAt_of_badBound bad_950
  refine ⟨N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15, fun
      n hn => ?_⟩
  exact ⟨h0 n (by omega), h1 n (by omega), h2 n (by omega), h3 n (by omega), h4 n (by omega),
      h5 n (by omega), h6 n (by omega), h7 n (by omega), h8 n (by omega), h9 n (by omega),
      h10 n (by omega), h11 n (by omega), h12 n (by omega), h13 n (by omega), h14 n (by omega),
      h15 n (by omega)⟩

/-- The unit construction covers `μ_T ≥ 9n/50`. -/
theorem open_T {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 9 * (n : ℝ) ≤ 50 * (Pool23 n \ A).card) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  have hμTn : (μT : ℝ) ≤ n / 3 := by
    have hTn : T n = n / 2 + n / 3 - n / 6 := rfl
    have : 3 * μT ≤ n := by omega
    have : (3 : ℝ) * μT ≤ n := by exact_mod_cast this
    linarith
  rcases le_or_gt (μT : ℝ) (23 / 100 * n + 1) with h | h
  · exact t_box hn hA hcard hl2 hl (9 / 50 : ℚ) (23 / 100 : ℚ) (673 / 1000 : ℚ) (33 / 40 : ℚ)
        (33 / 40 : ℚ) (27 / 40 : ℚ) (33 / 40 : ℚ) (33 / 40 : ℚ) (353 / 10000 : ℚ) (1517 / 5000 : ℚ)
        (1517 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith) hb.b675 hb.b825 hb.b825
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
  · rcases le_or_gt (μT : ℝ) (33 / 100 * n + 1) with h | h
    · exact t_box hn hA hcard hl2 hl (23 / 100 : ℚ) (33 / 100 : ℚ) (187 / 250 : ℚ) (17 / 20 : ℚ)
          (9 / 10 : ℚ) (3 / 4 : ℚ) (17 / 20 : ℚ) (9 / 10 : ℚ) (143 / 1250 : ℚ) (3457 / 10000 : ℚ)
          (4637 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith) hb.b750 hb.b850
          hb.b900 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact t_box hn hA hcard hl2 hl (33 / 100 : ℚ) (1 / 3 : ℚ) (1501 / 2000 : ℚ) (4 / 5 : ℚ)
          (19 / 20 : ℚ) (31 / 40 : ℚ) (4 / 5 : ℚ) (19 / 20 : ℚ) (1049 / 5000 : ℚ)
          (2483 / 10000 : ℚ) (7107 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
          hb.b775 hb.b800 hb.b950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `3 / 70 ≤ 3d/n ≤ 13 / 140`. -/
theorem open_GP_0 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (3 / 70 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 13 / 140 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 20 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (3 / 70 : ℚ) (13 / 140 : ℚ) (0 : ℚ) (1 / 20 : ℚ) (13 / 20 : ℚ)
        (17 / 20 : ℚ) (7657 / 14000 : ℚ) (13 / 20 : ℚ) (13 / 20 : ℚ) (0 : ℚ) (13 / 20 : ℚ)
        (17 / 20 : ℚ) (11 / 20 : ℚ) (13 / 20 : ℚ) (89 / 5000 : ℚ) (3457 / 10000 : ℚ)
        (3 / 10000 : ℚ) (89 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b650 hb.b850 hb.b550 hb.b650
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · exact gp_box hn hA hcard hl2 hl (3 / 70 : ℚ) (13 / 140 : ℚ) (1 / 20 : ℚ) (29 / 175 : ℚ)
        (7 / 10 : ℚ) (17 / 20 : ℚ) (1041 / 1750 : ℚ) (7 / 10 : ℚ) (7 / 10 : ℚ) (671 / 42000 : ℚ)
        (7 / 10 : ℚ) (17 / 20 : ℚ) (3 / 5 : ℚ) (7 / 10 : ℚ) (251 / 5000 : ℚ) (3457 / 10000 : ℚ)
        (7 / 2000 : ℚ) (251 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b700 hb.b850 hb.b600 hb.b700
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (fun h => by norm_num at h)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `13 / 140 ≤ 3d/n ≤ 27 / 140`. -/
theorem open_GP_1 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (13 / 140 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 27 / 140 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 20 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (13 / 140 : ℚ) (27 / 140 : ℚ) (0 : ℚ) (1 / 20 : ℚ) (7 / 10 : ℚ)
        (7 / 8 : ℚ) (4231 / 7000 : ℚ) (7 / 10 : ℚ) (7 / 10 : ℚ) (1 / 400 : ℚ) (7 / 10 : ℚ)
        (7 / 8 : ℚ) (5 / 8 : ℚ) (7 / 10 : ℚ) (251 / 5000 : ℚ) (3939 / 10000 : ℚ) (1 / 125 : ℚ)
        (251 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) hb.b700 hb.b875 hb.b625 hb.b700 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · rcases le_or_gt (μ6 : ℝ) (3 / 40 * n) with ha | ha
    · exact gp_box hn hA hcard hl2 hl (13 / 140 : ℚ) (27 / 140 : ℚ) (1 / 20 : ℚ) (3 / 40 : ℚ)
          (29 / 40 : ℚ) (9 / 10 : ℚ) (8987 / 14000 : ℚ) (31 / 40 : ℚ) (29 / 40 : ℚ) (3 / 200 : ℚ)
          (29 / 40 : ℚ) (9 / 10 : ℚ) (13 / 20 : ℚ) (31 / 40 : ℚ) (93 / 1250 : ℚ) (4637 / 10000 : ℚ)
          (89 / 5000 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) hb.b725 hb.b900 hb.b650 hb.b775
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    · exact gp_box hn hA hcard hl2 hl (13 / 140 : ℚ) (27 / 140 : ℚ) (3 / 40 : ℚ) (313 / 2100 : ℚ)
          (31 / 40 : ℚ) (9 / 10 : ℚ) (608 / 875 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (457 / 14000 : ℚ)
          (31 / 40 : ℚ) (9 / 10 : ℚ) (7 / 10 : ℚ) (31 / 40 : ℚ) (1049 / 5000 : ℚ)
          (4637 / 10000 : ℚ) (251 / 5000 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b775
          hb.b900 hb.b700 hb.b775 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (fun h => by norm_num at h)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `27 / 140 ≤ 3d/n ≤ 41 / 140`. -/
theorem open_GP_2 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (27 / 140 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 41 / 140 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 40 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (0 : ℚ) (1 / 40 : ℚ) (3 / 4 : ℚ)
        (7 / 8 : ℚ) (9057 / 14000 : ℚ) (27 / 40 : ℚ) (27 / 40 : ℚ) (0 : ℚ) (3 / 4 : ℚ) (7 / 8 : ℚ)
        (13 / 20 : ℚ) (27 / 40 : ℚ) (143 / 1250 : ℚ) (3939 / 10000 : ℚ) (89 / 5000 : ℚ)
        (353 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b750 hb.b875 hb.b650 hb.b675
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · rcases le_or_gt (μ6 : ℝ) (1 / 20 * n) with ha | ha
    · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (1 / 40 : ℚ) (1 / 20 : ℚ)
          (3 / 4 : ℚ) (9 / 10 : ℚ) (2343 / 3500 : ℚ) (3 / 4 : ℚ) (3 / 4 : ℚ) (3 / 400 : ℚ)
          (3 / 4 : ℚ) (9 / 10 : ℚ) (27 / 40 : ℚ) (3 / 4 : ℚ) (143 / 1250 : ℚ) (4637 / 10000 : ℚ)
          (353 / 10000 : ℚ) (143 / 1250 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) hb.b750 hb.b900 hb.b675 hb.b750
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    · rcases le_or_gt (μ6 : ℝ) (3 / 40 * n) with ha | ha
      · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (1 / 20 : ℚ) (3 / 40 : ℚ)
            (31 / 40 : ℚ) (37 / 40 : ℚ) (9897 / 14000 : ℚ) (33 / 40 : ℚ) (31 / 40 : ℚ) (1 / 50 : ℚ)
            (31 / 40 : ℚ) (37 / 40 : ℚ) (29 / 40 : ℚ) (33 / 40 : ℚ) (1049 / 5000 : ℚ)
            (5387 / 10000 : ℚ) (93 / 1250 : ℚ) (1517 / 5000 : ℚ) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b775
            hb.b925 hb.b725 hb.b825 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
      · rcases le_or_gt (μ6 : ℝ) (7 / 80 * n) with ha | ha
        · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (3 / 40 : ℚ) (7 / 80 : ℚ)
              (4 / 5 : ℚ) (37 / 40 : ℚ) (10107 / 14000 : ℚ) (17 / 20 : ℚ) (4 / 5 : ℚ) (1 / 40 : ℚ)
              (4 / 5 : ℚ) (37 / 40 : ℚ) (29 / 40 : ℚ) (17 / 20 : ℚ) (2483 / 10000 : ℚ)
              (5387 / 10000 : ℚ) (93 / 1250 : ℚ) (3457 / 10000 : ℚ) (by push_cast; linarith)
              (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b800
              hb.b925 hb.b725 hb.b850 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
        · rcases le_or_gt (μ6 : ℝ) (3 / 32 * n) with ha | ha
          · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (7 / 80 : ℚ) (3 / 32 : ℚ)
                (4 / 5 : ℚ) (37 / 40 : ℚ) (2553 / 3500 : ℚ) (7 / 8 : ℚ) (4 / 5 : ℚ) (11 / 400 : ℚ)
                (4 / 5 : ℚ) (37 / 40 : ℚ) (3 / 4 : ℚ) (7 / 8 : ℚ) (2483 / 10000 : ℚ)
                (5387 / 10000 : ℚ) (143 / 1250 : ℚ) (3939 / 10000 : ℚ) (by push_cast; linarith)
                (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b800
                hb.b925 hb.b750 hb.b875 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
          · rcases le_or_gt (μ6 : ℝ) (17 / 160 * n) with ha | ha
            · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (3 / 32 : ℚ)
                  (17 / 160 : ℚ) (33 / 40 : ℚ) (37 / 40 : ℚ) (5211 / 7000 : ℚ) (9 / 10 : ℚ)
                  (33 / 40 : ℚ) (13 / 400 : ℚ) (33 / 40 : ℚ) (37 / 40 : ℚ) (3 / 4 : ℚ) (9 / 10 : ℚ)
                  (1517 / 5000 : ℚ) (5387 / 10000 : ℚ) (143 / 1250 : ℚ) (4637 / 10000 : ℚ)
                  (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
                  (by push_cast; linarith) hb.b825 hb.b925 hb.b750 hb.b900 (by norm_num)
                  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
            · rcases le_or_gt (μ6 : ℝ) (7 / 64 * n) with ha | ha
              · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (17 / 160 : ℚ)
                    (7 / 64 : ℚ) (33 / 40 : ℚ) (37 / 40 : ℚ) (10527 / 14000 : ℚ) (9 / 10 : ℚ)
                    (33 / 40 : ℚ) (7 / 200 : ℚ) (33 / 40 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ)
                    (9 / 10 : ℚ) (1517 / 5000 : ℚ) (5387 / 10000 : ℚ) (1049 / 5000 : ℚ)
                    (4637 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
                    (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b925 hb.b775
                    hb.b900 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
              · exact gp_box hn hA hcard hl2 hl (27 / 140 : ℚ) (41 / 140 : ℚ) (7 / 64 : ℚ)
                    (81 / 700 : ℚ) (17 / 20 : ℚ) (37 / 40 : ℚ) (10737 / 14000 : ℚ) (9 / 10 : ℚ)
                    (17 / 20 : ℚ) (1 / 25 : ℚ) (17 / 20 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ)
                    (9 / 10 : ℚ) (3457 / 10000 : ℚ) (5387 / 10000 : ℚ) (1049 / 5000 : ℚ)
                    (4637 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
                    (by push_cast; linarith) (by push_cast; linarith) hb.b850 hb.b925 hb.b775
                    hb.b900 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `41 / 140 ≤ 3d/n ≤ 12 / 35`. -/
theorem open_GP_3 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (41 / 140 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 12 / 35 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 40 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (41 / 140 : ℚ) (12 / 35 : ℚ) (0 : ℚ) (1 / 40 : ℚ) (3 / 4 : ℚ)
        (9 / 10 : ℚ) (9407 / 14000 : ℚ) (29 / 40 : ℚ) (29 / 40 : ℚ) (0 : ℚ) (3 / 4 : ℚ)
        (9 / 10 : ℚ) (27 / 40 : ℚ) (29 / 40 : ℚ) (143 / 1250 : ℚ) (4637 / 10000 : ℚ)
        (353 / 10000 : ℚ) (93 / 1250 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b750 hb.b900 hb.b675 hb.b725
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · rcases le_or_gt (μ6 : ℝ) (1 / 20 * n) with ha | ha
    · exact gp_box hn hA hcard hl2 hl (41 / 140 : ℚ) (12 / 35 : ℚ) (1 / 40 : ℚ) (1 / 20 : ℚ)
          (31 / 40 : ℚ) (37 / 40 : ℚ) (9827 / 14000 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (1 / 100 : ℚ)
          (31 / 40 : ℚ) (37 / 40 : ℚ) (29 / 40 : ℚ) (31 / 40 : ℚ) (1049 / 5000 : ℚ)
          (5387 / 10000 : ℚ) (93 / 1250 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b775
          hb.b925 hb.b725 hb.b775 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    · rcases le_or_gt (μ6 : ℝ) (3 / 40 * n) with ha | ha
      · exact gp_box hn hA hcard hl2 hl (41 / 140 : ℚ) (12 / 35 : ℚ) (1 / 20 : ℚ) (3 / 40 : ℚ)
            (4 / 5 : ℚ) (37 / 40 : ℚ) (10247 / 14000 : ℚ) (17 / 20 : ℚ) (4 / 5 : ℚ) (1 / 50 : ℚ)
            (4 / 5 : ℚ) (37 / 40 : ℚ) (3 / 4 : ℚ) (17 / 20 : ℚ) (2483 / 10000 : ℚ)
            (5387 / 10000 : ℚ) (143 / 1250 : ℚ) (3457 / 10000 : ℚ) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b800
            hb.b925 hb.b750 hb.b850 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
      · exact gp_box hn hA hcard hl2 hl (41 / 140 : ℚ) (12 / 35 : ℚ) (3 / 40 : ℚ) (173 / 2100 : ℚ)
            (33 / 40 : ℚ) (9 / 10 : ℚ) (10247 / 14000 : ℚ) (7 / 8 : ℚ) (33 / 40 : ℚ) (1 / 50 : ℚ)
            (33 / 40 : ℚ) (9 / 10 : ℚ) (3 / 4 : ℚ) (7 / 8 : ℚ) (1517 / 5000 : ℚ) (4637 / 10000 : ℚ)
            (143 / 1250 : ℚ) (3939 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b900 hb.b750 hb.b875
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
            (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `12 / 35 ≤ 3d/n ≤ 11 / 28`. -/
theorem open_GP_4 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (12 / 35 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 11 / 28 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 40 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (12 / 35 : ℚ) (11 / 28 : ℚ) (0 : ℚ) (1 / 40 : ℚ) (31 / 40 : ℚ)
        (9 / 10 : ℚ) (9757 / 14000 : ℚ) (3 / 4 : ℚ) (3 / 4 : ℚ) (0 : ℚ) (31 / 40 : ℚ) (9 / 10 : ℚ)
        (7 / 10 : ℚ) (3 / 4 : ℚ) (1049 / 5000 : ℚ) (4637 / 10000 : ℚ) (251 / 5000 : ℚ)
        (143 / 1250 : ℚ) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) hb.b775 hb.b900 hb.b700 hb.b750 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · rcases le_or_gt (μ6 : ℝ) (1 / 20 * n) with ha | ha
    · exact gp_box hn hA hcard hl2 hl (12 / 35 : ℚ) (11 / 28 : ℚ) (1 / 40 : ℚ) (1 / 20 : ℚ)
          (4 / 5 : ℚ) (37 / 40 : ℚ) (10177 / 14000 : ℚ) (4 / 5 : ℚ) (4 / 5 : ℚ) (1 / 100 : ℚ)
          (4 / 5 : ℚ) (37 / 40 : ℚ) (3 / 4 : ℚ) (4 / 5 : ℚ) (2483 / 10000 : ℚ) (5387 / 10000 : ℚ)
          (143 / 1250 : ℚ) (2483 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) hb.b800 hb.b925 hb.b750 hb.b800
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    · exact gp_box hn hA hcard hl2 hl (12 / 35 : ℚ) (11 / 28 : ℚ) (1 / 20 : ℚ) (23 / 350 : ℚ)
          (33 / 40 : ℚ) (9 / 10 : ℚ) (10387 / 14000 : ℚ) (17 / 20 : ℚ) (33 / 40 : ℚ) (3 / 200 : ℚ)
          (33 / 40 : ℚ) (9 / 10 : ℚ) (3 / 4 : ℚ) (17 / 20 : ℚ) (1517 / 5000 : ℚ) (4637 / 10000 : ℚ)
          (143 / 1250 : ℚ) (3457 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b900 hb.b750 hb.b850
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `11 / 28 ≤ 3d/n ≤ 31 / 70`. -/
theorem open_GP_5 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (11 / 28 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 31 / 70 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 40 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (11 / 28 : ℚ) (31 / 70 : ℚ) (0 : ℚ) (1 / 40 : ℚ) (4 / 5 : ℚ)
        (37 / 40 : ℚ) (10317 / 14000 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (1 / 200 : ℚ) (4 / 5 : ℚ)
        (37 / 40 : ℚ) (3 / 4 : ℚ) (31 / 40 : ℚ) (2483 / 10000 : ℚ) (5387 / 10000 : ℚ)
        (143 / 1250 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b800 hb.b925 hb.b750 hb.b775
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · exact gp_box hn hA hcard hl2 hl (11 / 28 : ℚ) (31 / 70 : ℚ) (1 / 40 : ℚ) (103 / 2100 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (1329 / 1750 : ℚ) (33 / 40 : ℚ) (33 / 40 : ℚ) (1 / 80 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (33 / 40 : ℚ) (1517 / 5000 : ℚ)
        (5387 / 10000 : ℚ) (1049 / 5000 : ℚ) (1517 / 5000 : ℚ) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b925
        hb.b775 hb.b825 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `31 / 70 ≤ 3d/n ≤ 131 / 280`. -/
theorem open_GP_6 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (31 / 70 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 131 / 280 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 80 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (31 / 70 : ℚ) (131 / 280 : ℚ) (0 : ℚ) (1 / 80 : ℚ) (4 / 5 : ℚ)
        (37 / 40 : ℚ) (5141 / 7000 : ℚ) (3 / 4 : ℚ) (3 / 4 : ℚ) (0 : ℚ) (4 / 5 : ℚ) (37 / 40 : ℚ)
        (3 / 4 : ℚ) (3 / 4 : ℚ) (2483 / 10000 : ℚ) (5387 / 10000 : ℚ) (143 / 1250 : ℚ)
        (143 / 1250 : ℚ) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) hb.b800 hb.b925 hb.b750 hb.b750 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · exact gp_box hn hA hcard hl2 hl (31 / 70 : ℚ) (131 / 280 : ℚ) (1 / 80 : ℚ) (17 / 525 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (2623 / 3500 : ℚ) (4 / 5 : ℚ) (4 / 5 : ℚ) (1 / 200 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (3 / 4 : ℚ) (4 / 5 : ℚ) (1517 / 5000 : ℚ) (5387 / 10000 : ℚ)
        (143 / 1250 : ℚ) (2483 / 10000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b925 hb.b750 hb.b800
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `131 / 280 ≤ 3d/n ≤ 29 / 56`. -/
theorem open_GP_7 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (131 / 280 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 29 / 56 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  rcases le_or_gt (μ6 : ℝ) (1 / 80 * n) with ha | ha
  · exact gp_box hn hA hcard hl2 hl (131 / 280 : ℚ) (29 / 56 : ℚ) (0 : ℚ) (1 / 80 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (1329 / 1750 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (0 : ℚ)
        (33 / 40 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (1517 / 5000 : ℚ)
        (5387 / 10000 : ℚ) (1049 / 5000 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b925
        hb.b775 hb.b775 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
  · rcases le_or_gt (μ6 : ℝ) (3 / 160 * n) with ha | ha
    · exact gp_box hn hA hcard hl2 hl (131 / 280 : ℚ) (29 / 56 : ℚ) (1 / 80 : ℚ) (3 / 160 : ℚ)
          (33 / 40 : ℚ) (37 / 40 : ℚ) (1329 / 1750 : ℚ) (4 / 5 : ℚ) (4 / 5 : ℚ) (0 : ℚ)
          (33 / 40 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (4 / 5 : ℚ) (1517 / 5000 : ℚ)
          (5387 / 10000 : ℚ) (1049 / 5000 : ℚ) (2483 / 10000 : ℚ) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b825
          hb.b925 hb.b775 hb.b800 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    · exact gp_box hn hA hcard hl2 hl (131 / 280 : ℚ) (29 / 56 : ℚ) (3 / 160 : ℚ) (101 / 4200 : ℚ)
          (17 / 20 : ℚ) (37 / 40 : ℚ) (5421 / 7000 : ℚ) (4 / 5 : ℚ) (4 / 5 : ℚ) (1 / 200 : ℚ)
          (17 / 20 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (4 / 5 : ℚ) (3457 / 10000 : ℚ)
          (5387 / 10000 : ℚ) (1049 / 5000 : ℚ) (2483 / 10000 : ℚ) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hb.b850
          hb.b925 hb.b775 hb.b800 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `29 / 56 ≤ 3d/n ≤ 587 / 1120`. -/
theorem open_GP_8 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (29 / 56 : ℝ) * n ≤ 3 * (Estar n \ A).card) (hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 587 / 1120 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  exact gp_box hn hA hcard hl2 hl (29 / 56 : ℚ) (587 / 1120 : ℚ) (0 : ℚ) (31 / 4200 : ℚ)
      (33 / 40 : ℚ) (37 / 40 : ℚ) (42703 / 56000 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (0 : ℚ)
      (33 / 40 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (1517 / 5000 : ℚ) (5387 / 10000 : ℚ)
      (1049 / 5000 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) hb.b825 hb.b925 hb.b775 hb.b775
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `587 / 1120 ≤ 3d/n ≤ 27 / 50`. -/
theorem open_GP_9 {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (587 / 1120 : ℝ) * n ≤ 3 * (Estar n \ A).card) (_hδ1 : 3 * ((Estar n \ A).card : ℝ) ≤ 27 / 50 * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
  exact gp_box hn hA hcard hl2 hl (587 / 1120 : ℚ) (27 / 50 : ℚ) (0 : ℚ) (89 / 16800 : ℚ)
      (17 / 20 : ℚ) (37 / 40 : ℚ) (1541 / 2000 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (0 : ℚ)
      (17 / 20 : ℚ) (37 / 40 : ℚ) (31 / 40 : ℚ) (31 / 40 : ℚ) (3457 / 10000 : ℚ) (5387 / 10000 : ℚ)
      (1049 / 5000 : ℚ) (1049 / 5000 : ℚ) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) hb.b850 hb.b925 hb.b775 hb.b775
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)

/-- **The open case.** If `A` omits more than `n/70` elements of `E*(n)`, the coprime graph of `A`
still contains every cycle of length `2l + 1` with `2 ≤ l ≤ n/6`. -/
theorem open_case {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) (hD : n < 70 * (Estar n \ A).card) {l : ℕ} (hl2 : 2 ≤ l)
    (hl : 6 * l ≤ n) : HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdR : (n : ℝ) < 70 * d := by exact_mod_cast hD
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  rcases le_or_gt (9 * (n : ℝ)) (50 * μT) with hT | hT
  · exact open_T hn hb hA hcard hl2 hl hT
  · rcases le_or_gt (3 * (d : ℝ)) (13 / 140 * n) with hδ | hδ
    · exact open_GP_0 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
    · rcases le_or_gt (3 * (d : ℝ)) (27 / 140 * n) with hδ | hδ
      · exact open_GP_1 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
      · rcases le_or_gt (3 * (d : ℝ)) (41 / 140 * n) with hδ | hδ
        · exact open_GP_2 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
        · rcases le_or_gt (3 * (d : ℝ)) (12 / 35 * n) with hδ | hδ
          · exact open_GP_3 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
          · rcases le_or_gt (3 * (d : ℝ)) (11 / 28 * n) with hδ | hδ
            · exact open_GP_4 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
            · rcases le_or_gt (3 * (d : ℝ)) (31 / 70 * n) with hδ | hδ
              · exact open_GP_5 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
              · rcases le_or_gt (3 * (d : ℝ)) (131 / 280 * n) with hδ | hδ
                · exact open_GP_6 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
                · rcases le_or_gt (3 * (d : ℝ)) (29 / 56 * n) with hδ | hδ
                  · exact open_GP_7 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
                  · rcases le_or_gt (3 * (d : ℝ)) (587 / 1120 * n) with hδ | hδ
                    · exact open_GP_8 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)
                    · exact open_GP_9 hn hb hA hcard hl2 hl hT (by linarith) (by linarith)

/-- **Erdős Problem #883, Question 1**, formally verified: for all large `n`, every `A ⊆ [1, n]`
with `|A| > T(n)` has a coprime graph containing every odd cycle of length at most `n/3 + 1`. -/
theorem question1 : Question1 := by
  obtain ⟨n₀, h₀⟩ := question1_restricted
  obtain ⟨Nb, hNb⟩ := bads_eventually
  refine ⟨n₀ + N₁ + Nb, fun n hn A hA hcard L hL h3 hLn => ?_⟩
  have hn13 : 13 ≤ n := le_trans (by unfold N₁; norm_num) (show N₁ ≤ n by omega)
  by_cases hD : 70 * (Estar n \ A).card ≤ n
  · exact h₀ n (by omega) A hA hcard hD L hL h3 hLn
  · obtain ⟨l, rfl⟩ := hL
    rcases (by omega : l = 1 ∨ 2 ≤ l) with rfl | hl2
    · exact triangle hn13 A hA hcard
    · exact open_case (by omega) (hNb n (by omega)) hA hcard (by omega) hl2 (by omega)

end ErdosSar
