import ErdosSar.OpenSetup

/-!
# The giant path

For `Q ≥ 1` the list `g₁, e₁, w₀, y₀, w₁, y₁, …, y_{Q-2}, w_{Q-1}, g₂` of length `2Q + 2`,
written as the image of `[0, 2Q + 2)` under the position map `gpF`.
-/

namespace ErdosSar

/-- The vertex at position `j` of the giant path. -/
def gpF (Q g1 e1 g2 : ℕ) (w y : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = 0 then g1 else if j = 1 then e1 else if j = 2 * Q + 1 then g2
  else if j % 2 = 0 then w ((j - 2) / 2) else y ((j - 3) / 2)

/-- The giant path `g₁, e₁, w₀, y₀, …, y_{Q-2}, w_{Q-1}, g₂`. -/
def gpPath (Q g1 e1 g2 : ℕ) (w y : ℕ → ℕ) : List ℕ :=
  (List.range (2 * Q + 2)).map (gpF Q g1 e1 g2 w y)

variable {Q g1 e1 g2 : ℕ} {w y : ℕ → ℕ}

theorem gpF_zero : gpF Q g1 e1 g2 w y 0 = g1 := by simp [gpF]

theorem gpF_one : gpF Q g1 e1 g2 w y 1 = e1 := by simp [gpF]

theorem gpF_last (hQ : 1 ≤ Q) : gpF Q g1 e1 g2 w y (2 * Q + 1) = g2 := by
  have h1 : Q ≠ 0 := by omega
  simp [gpF, h1]

theorem gpF_w {i : ℕ} (_hi : i < Q) : gpF Q g1 e1 g2 w y (2 * i + 2) = w i := by
  have h1 : 2 * i + 2 ≠ 0 := by omega
  have h2 : 2 * i + 2 ≠ 1 := by omega
  have h3 : 2 * i + 2 ≠ 2 * Q + 1 := by omega
  have h4 : (2 * i + 2) % 2 = 0 := by omega
  have h5 : (2 * i + 2 - 2) / 2 = i := by omega
  simp only [gpF, h1, h2, h3, h4, h5, ite_false, ite_true]

theorem gpF_y {i : ℕ} (hi : i + 1 < Q) : gpF Q g1 e1 g2 w y (2 * i + 3) = y i := by
  have h1 : 2 * i + 3 ≠ 0 := by omega
  have h2 : 2 * i + 3 ≠ 1 := by omega
  have h3 : 2 * i + 3 ≠ 2 * Q + 1 := by omega
  have h4 : ¬ (2 * i + 3) % 2 = 0 := by omega
  have h5 : (2 * i + 3 - 3) / 2 = i := by omega
  simp only [gpF, h1, h2, h3, h4, h5, ite_false]

theorem gp_index_cases {j : ℕ} (_hQ : 1 ≤ Q) (hj : j < 2 * Q + 2) :
    j = 0 ∨ j = 1 ∨ j = 2 * Q + 1 ∨ (∃ i < Q, j = 2 * i + 2) ∨ (∃ i, i + 1 < Q ∧ j = 2 * i + 3) := by
  rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
  · rcases Nat.eq_zero_or_pos r with h | h
    · left; omega
    · right; right; right; left; exact ⟨r - 1, by omega, by omega⟩
  · rcases Nat.eq_zero_or_pos r with h | h
    · right; left; omega
    · rcases (by omega : r = Q ∨ r < Q) with h' | h'
      · right; right; left; omega
      · right; right; right; right; exact ⟨r - 1, by omega, by omega⟩

theorem gpPath_length : (gpPath Q g1 e1 g2 w y).length = 2 * Q + 2 := by
  simp [gpPath]

theorem gpPath_ne_nil : gpPath Q g1 e1 g2 w y ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [gpPath_length] at this
  simp at this

theorem gpPath_head : (gpPath Q g1 e1 g2 w y).headD 0 = g1 := by
  unfold gpPath
  rw [List.range_succ_eq_map]
  simp [gpF_zero]

theorem gpPath_last (hQ : 1 ≤ Q) : (gpPath Q g1 e1 g2 w y).getLastD 0 = g2 := by
  unfold gpPath
  rw [show 2 * Q + 2 = (2 * Q + 1) + 1 by ring, List.range_succ, List.map_append]
  simp [gpF_last hQ]

theorem mem_gpPath (hQ : 1 ≤ Q) {v : ℕ} (hv : v ∈ gpPath Q g1 e1 g2 w y) :
    v = g1 ∨ v = e1 ∨ v = g2 ∨ (∃ i < Q, v = w i) ∨ (∃ i, i + 1 < Q ∧ v = y i) := by
  unfold gpPath at hv
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
  have hj' := List.mem_range.1 hj
  rcases gp_index_cases hQ hj' with rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · left; exact gpF_zero
  · right; left; exact gpF_one
  · right; right; left; exact gpF_last hQ
  · right; right; right; left; exact ⟨i, hi, gpF_w hi⟩
  · right; right; right; right; exact ⟨i, hi, gpF_y hi⟩

theorem gpPath_chain (hQ : 1 ≤ Q) (h01 : Nat.Coprime g1 e1) (h12 : Nat.Coprime e1 (w 0))
    (hwy : ∀ i, i + 1 < Q → Nat.Coprime (w i) (y i))
    (hyw : ∀ i, i + 1 < Q → Nat.Coprime (y i) (w (i + 1)))
    (hlast : Nat.Coprime (w (Q - 1)) g2) :
    (gpPath Q g1 e1 g2 w y).IsChain Nat.Coprime := by
  unfold gpPath
  rw [List.isChain_map, show 2 * Q + 2 = (2 * Q + 1) + 1 by ring, List.isChain_range_succ]
  intro j hj
  simp only [Nat.succ_eq_add_one]
  rcases gp_index_cases hQ (show j < 2 * Q + 2 by omega) with rfl | rfl | rfl | ⟨i, hi, rfl⟩ |
    ⟨i, hi, rfl⟩
  · rw [gpF_zero, gpF_one]; exact h01
  · rw [gpF_one, show 1 + 1 = 2 * 0 + 2 by rfl, gpF_w (by omega)]; exact h12
  · omega
  · rw [gpF_w hi]
    rcases (by omega : i + 1 < Q ∨ i + 1 = Q) with h | h
    · rw [show 2 * i + 2 + 1 = 2 * i + 3 by ring, gpF_y h]; exact hwy i h
    · rw [show 2 * i + 2 + 1 = 2 * Q + 1 by omega, gpF_last hQ]
      rw [show i = Q - 1 by omega]; exact hlast
  · rw [gpF_y hi, show 2 * i + 3 + 1 = 2 * (i + 1) + 2 by ring, gpF_w hi]; exact hyw i hi

theorem gpPath_nodup (hQ : 1 ≤ Q) (hg12 : g1 ≠ g2) (hg1e : g1 ≠ e1) (he1g2 : e1 ≠ g2)
    (hg1w : ∀ i < Q, g1 ≠ w i) (hg1y : ∀ i, i + 1 < Q → g1 ≠ y i)
    (he1w : ∀ i < Q, e1 ≠ w i) (he1y : ∀ i, i + 1 < Q → e1 ≠ y i)
    (hg2w : ∀ i < Q, g2 ≠ w i) (hg2y : ∀ i, i + 1 < Q → g2 ≠ y i)
    (hwy : ∀ i < Q, ∀ i', i' + 1 < Q → w i ≠ y i')
    (hwinj : ∀ i < Q, ∀ i' < Q, w i = w i' → i = i')
    (hyinj : ∀ i, i + 1 < Q → ∀ i', i' + 1 < Q → y i = y i' → i = i') :
    (gpPath Q g1 e1 g2 w y).Nodup := by
  unfold gpPath
  refine List.Nodup.map_on ?_ List.nodup_range
  intro j hj j' hj' h
  have hj1 := List.mem_range.1 hj
  have hj1' := List.mem_range.1 hj'
  rcases gp_index_cases hQ hj1 with rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
  rcases gp_index_cases hQ hj1' with rfl | rfl | rfl | ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩ <;>
  simp (disch := omega) only [gpF_zero, gpF_one, gpF_last, gpF_w, gpF_y] at h
  all_goals first
    | rfl
    | exact absurd h hg1e | exact absurd h.symm hg1e
    | exact absurd h hg12 | exact absurd h.symm hg12
    | exact absurd h he1g2 | exact absurd h.symm he1g2
    | exact absurd h (hg1w _ ‹_›) | exact absurd h.symm (hg1w _ ‹_›)
    | exact absurd h (hg1y _ ‹_›) | exact absurd h.symm (hg1y _ ‹_›)
    | exact absurd h (he1w _ ‹_›) | exact absurd h.symm (he1w _ ‹_›)
    | exact absurd h (he1y _ ‹_›) | exact absurd h.symm (he1y _ ‹_›)
    | exact absurd h (hg2w _ ‹_›) | exact absurd h.symm (hg2w _ ‹_›)
    | exact absurd h (hg2y _ ‹_›) | exact absurd h.symm (hg2y _ ‹_›)
    | exact absurd h (hwy _ hi _ hi') | exact absurd h.symm (hwy _ hi' _ hi)
    | (have := hwinj _ hi _ hi' h; omega)
    | (have := hyinj _ hi _ hi' h; omega)

end ErdosSar
