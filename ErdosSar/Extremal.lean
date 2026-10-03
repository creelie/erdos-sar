import ErdosSar.Defs

/-!
# Sharpness of Question 1

* `card_M23`, `not_hasCycle3_M23`: the multiples of `2` or `3` in `[1, n]` form a set of
  size exactly `T n` whose coprime graph has no triangle, so the hypothesis `|A| > T n`
  cannot be weakened.
* `odd_cycle_length_bound`: in the coprime graph of any finite `A`, an odd cycle of
  length `L` satisfies `L + 1 ≤ 2 · #{odd elements of A}`. Hence a set consisting of
  even numbers together with `o n + 1` odd numbers (which has `T n + 1` elements when it
  contains all even numbers of `[1, n]`) has no odd cycle longer than `2 · o n + 1`.
-/

namespace ErdosSar

/-- The multiples of `2` or `3` in `[1, n]`. -/
def M23 (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun x => 2 ∣ x ∨ 3 ∣ x)

/-- Split `n = 6k + r` with `r < 6`; useful for `omega` goals involving `n / 2`, `n / 3`, `n / 6`. -/
theorem exists_six_mul_add (n : ℕ) : ∃ k r, r < 6 ∧ n = 6 * k + r :=
  ⟨n / 6, n % 6, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 6).symm⟩

theorem T_succ (n : ℕ) : T (n + 1) = T n + if 2 ∣ n + 1 ∨ 3 ∣ n + 1 then 1 else 0 := by
  obtain ⟨k, r, hr, rfl⟩ := exists_six_mul_add n
  simp only [T]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> omega

theorem card_M23 (n : ℕ) : (M23 n).card = T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hc : 2 ∣ n + 1 ∨ 3 ∣ n + 1
    · have h : M23 (n + 1) = insert (n + 1) (M23 n) := by
        ext x
        simp only [M23, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
        constructor
        · intro h; omega
        · intro h; omega
      rw [h, Finset.card_insert_of_notMem (by simp [M23]), ih, T_succ]
      simp [hc]
    · have h : M23 (n + 1) = M23 n := by
        ext x
        simp only [M23, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro h; omega
        · intro h; omega
      rw [h, ih, T_succ]
      simp [hc]

theorem no_triangle_M23 {n : ℕ} (x y z : M23 n) (h1 : (coprimeGraph (M23 n)).Adj x y)
    (h2 : (coprimeGraph (M23 n)).Adj y z) (h3 : (coprimeGraph (M23 n)).Adj z x) : False := by
  have mem : ∀ w : M23 n, 2 ∣ (w : ℕ) ∨ 3 ∣ (w : ℕ) := fun w => (Finset.mem_filter.1 w.2).2
  rcases mem x with hx | hx <;> rcases mem y with hy | hy <;> rcases mem z with hz | hz <;>
    first
    | exact absurd (Nat.eq_one_of_dvd_coprimes h1.2 hx hy) (by decide)
    | exact absurd (Nat.eq_one_of_dvd_coprimes h2.2 hy hz) (by decide)
    | exact absurd (Nat.eq_one_of_dvd_coprimes h3.2 hz hx) (by decide)

theorem not_hasCycle3_M23 (n : ℕ) : ¬ HasCycleOfLength (coprimeGraph (M23 n)) 3 := by
  rintro ⟨v, p, -, hl⟩
  cases p with
  | nil => simp at hl
  | cons h1 p =>
    cases p with
    | nil => simp at hl
    | cons h2 p =>
      cases p with
      | nil => simp at hl
      | cons h3 p =>
        cases p with
        | nil => exact no_triangle_M23 _ _ _ h1 h2 h3
        | cons _ _ => simp at hl

/-- In a graph in which the vertices satisfying `P` are pairwise non-adjacent, a cycle of
length `L` passes through at least `L / 2` vertices not satisfying `P`. -/
theorem IsCycle.length_le_two_mul_filter_not {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    [DecidablePred P] (hP : ∀ x y, P x → P y → ¬ G.Adj x y) {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) :
    p.length ≤ 2 * (p.support.tail.filter (fun x => ¬ P x)).length := by
  have hsplit := p.support.tail.length_eq_length_filter_add (fun x => decide (P x))
  have htail : p.support.tail.length = p.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]; rfl
  -- vertices satisfying `P` on the cycle, counted via the darts leaving them
  have hA : (p.support.tail.filter (fun x => decide (P x))).length =
      (p.darts.filter (fun d => decide (P d.fst))).length := by
    rw [(p.tail_support_perm_dropLast_support.filter _).length_eq,
      ← SimpleGraph.Walk.map_fst_darts, List.filter_map, List.length_map]
    rfl
  set l₁ := (p.darts.filter (fun d => decide (P d.fst))).map (·.snd) with hl₁
  have hnodup : l₁.Nodup := by
    have := hp.support_nodup
    rw [← SimpleGraph.Walk.map_snd_darts] at this
    exact this.sublist ((List.filter_sublist).map _)
  have hsub : l₁ ⊆ p.support.tail.filter (fun x => ¬ P x) := by
    intro y hy
    simp only [hl₁, List.mem_map, List.mem_filter, decide_eq_true_eq] at hy
    obtain ⟨d, ⟨hd, hPd⟩, rfl⟩ := hy
    simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, fun h => hP _ _ hPd h d.adj⟩
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map_of_mem hd
  have hle := (hnodup.subperm hsub).length_le
  rw [hl₁, List.length_map, ← hA] at hle
  have : (p.support.tail.filter (fun x => !decide (P x))).length =
      (p.support.tail.filter (fun x => ¬ P x)).length := by
    congr 1; apply List.filter_congr; intro x _; simp
  omega

/-- In the coprime graph of `A`, every odd cycle of length `L` uses at least `(L+1)/2`
odd numbers, so `L + 1 ≤ 2 · #{x ∈ A | x odd}`. -/
theorem odd_cycle_length_bound (A : Finset ℕ) {v : A} {p : (coprimeGraph A).Walk v v}
    (hp : p.IsCycle) (hodd : Odd p.length) :
    p.length + 1 ≤ 2 * (A.filter Odd).card := by
  have hP : ∀ x y : A, Even (x : ℕ) → Even (y : ℕ) → ¬ (coprimeGraph A).Adj x y := by
    intro x y hx hy hxy
    have := Nat.eq_one_of_dvd_coprimes hxy.2 (even_iff_two_dvd.1 hx) (even_iff_two_dvd.1 hy)
    omega
  have h1 := IsCycle.length_le_two_mul_filter_not (fun x : A => Even (x : ℕ)) hP hp
  set l := p.support.tail.filter (fun x : A => ¬ Even (x : ℕ))
  have hnd : (l.map Subtype.val).Nodup :=
    (hp.support_nodup.sublist List.filter_sublist).map Subtype.val_injective
  have hsub : (l.map Subtype.val).toFinset ⊆ A.filter Odd := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map, l, List.mem_filter, decide_eq_true_eq] at hy
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
    exact Finset.mem_filter.2 ⟨x.2, Nat.not_even_iff_odd.1 hx⟩
  have h2 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at h2
  obtain ⟨k, hk⟩ := hodd
  omega

end ErdosSar
