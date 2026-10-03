import Mathlib.Data.List.Rotate
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Jackson's theorem on long cycles in bipartite graphs

Let `r : α → β → Prop` be a bipartite adjacency relation, `X : Finset α`, `Y : Finset β`,
and `k` a natural number such that `2 ≤ |X| ≤ k`, `|Y| ≤ 2k - 2`, and every `x ∈ X` is
related to at least `k` elements of `Y`. Then there is a cycle `x₀ y₀ x₁ y₁ … x_{t-1} y_{t-1} x₀`
alternating between `X` and `Y` that passes through every element of `X`
(B. Jackson, *Cycles in bipartite graphs*, J. Combin. Theory Ser. B 30 (1981)).

Proof used here. Take a cycle through as many elements of `X` as possible and suppose
`x ∈ X` is missed. Let `s` be the number of neighbours of `x` on the cycle and let `S⁺` be
the `X`-vertices that follow them. The off-cycle neighbourhoods of `x` and of the elements
of `S⁺` are pairwise disjoint (otherwise the cycle could be extended), which gives
`(k - s) + s (k - t) ≤ |Y| - t`; with `t ≤ k - 1` and `|Y| ≤ 2k - 2` this forces `s = 0`.
If `s = 0`, two consecutive cycle vertices `a₀, a₁` each share at least two neighbours
with `x`, all off the cycle, and the cycle can again be extended.
-/

set_option linter.unusedSectionVars false

namespace ErdosSar.Jackson

variable {α β : Type*} (r : α → β → Prop)

/-- An alternating path `a₀ b₀ a₁ b₁ … aₘ` with `as = [a₀, …, aₘ]` and `bs = [b₀, …, b_{m-1}]`. -/
inductive APath : List α → List β → Prop
  | single (a : α) : APath [a] []
  | cons {a a' : α} {b : β} {as : List α} {bs : List β} :
      r a b → r a' b → APath (a' :: as) bs → APath (a :: a' :: as) (b :: bs)

variable {r}

namespace APath

theorem length_eq {as : List α} {bs : List β} (h : APath r as bs) :
    as.length = bs.length + 1 := by
  induction h with
  | single => rfl
  | cons _ _ _ ih => simp only [List.length_cons] at ih ⊢; omega

theorem ne_nil {as : List α} {bs : List β} (h : APath r as bs) : as ≠ [] := by
  cases h <;> simp

theorem append {as₁ as₂ : List α} {a : α} {bs₁ bs₂ : List β}
    (h₁ : APath r (as₁ ++ [a]) bs₁) (h₂ : APath r (a :: as₂) bs₂) :
    APath r (as₁ ++ a :: as₂) (bs₁ ++ bs₂) := by
  induction as₁ generalizing bs₁ with
  | nil =>
    cases h₁ with
    | single => simpa using h₂
  | cons c as₁ ih =>
    cases as₁ with
    | nil =>
      cases h₁ with
      | cons hb hb' h =>
        cases h with
        | single => exact APath.cons hb hb' h₂
    | cons d as₁ =>
      cases h₁ with
      | cons hb hb' h =>
        exact APath.cons hb hb' (ih h)

theorem snoc {as : List α} {a a' : α} {b : β} {bs : List β}
    (h : APath r (as ++ [a]) bs) (hb : r a b) (hb' : r a' b) :
    APath r (as ++ [a, a']) (bs ++ [b]) :=
  append h (APath.cons hb hb' (APath.single a'))

theorem reverse {as : List α} {bs : List β} (h : APath r as bs) :
    APath r as.reverse bs.reverse := by
  induction h with
  | single a => exact APath.single a
  | @cons a a' b as bs hb hb' _ ih =>
    rw [List.reverse_cons] at ih
    have := ih.snoc hb' hb
    simpa [List.reverse_cons] using this

theorem set_head {a a' : α} {as : List α} {b : β} {bs : List β}
    (h : APath r (a :: as) (b :: bs)) (hb : r a' b) : APath r (a' :: as) (b :: bs) := by
  cases h with
  | cons _ hb' h => exact APath.cons hb hb' h

theorem set_last {as : List α} {a a' : α} {b : β} {bs : List β}
    (h : APath r (as ++ [a]) (bs ++ [b])) (hb : r a' b) :
    APath r (as ++ [a']) (bs ++ [b]) := by
  have h' := h.reverse
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at h'
  have := (h'.set_head hb).reverse
  simpa using this

/-- Splitting an alternating path at its `n`-th `α`-vertex. -/
theorem split {as : List α} {bs : List β} (h : APath r as bs) (n : ℕ) (hn : n < as.length) :
    APath r (as.take (n + 1)) (bs.take n) ∧ APath r (as.drop n) (bs.drop n) := by
  induction h generalizing n with
  | single a =>
    simp only [List.length_singleton, Nat.lt_one_iff] at hn
    subst hn
    exact ⟨APath.single a, APath.single a⟩
  | @cons a a' b as bs hb hb' h ih =>
    cases n with
    | zero => exact ⟨by simpa using APath.single a, APath.cons hb hb' h⟩
    | succ n =>
      simp only [List.length_cons] at hn
      obtain ⟨h1, h2⟩ := ih n (by simpa using hn)
      refine ⟨?_, by simpa using h2⟩
      simp only [List.take_succ_cons]
      cases n with
      | zero => simpa using APath.cons hb hb' (APath.single a')
      | succ n =>
        simp only [List.take_succ_cons] at h1 ⊢
        exact APath.cons hb hb' h1

/-- Splitting an alternating path at a prescribed `α`-vertex. -/
theorem split_append {as₁ as₂ : List α} {c : α} {bs : List β}
    (h : APath r (as₁ ++ c :: as₂) bs) :
    APath r (as₁ ++ [c]) (bs.take as₁.length) ∧ APath r (c :: as₂) (bs.drop as₁.length) := by
  have := h.split as₁.length (by simp)
  simpa [List.take_append, List.drop_append, List.take_of_length_le] using this

end APath

/-- `as = [a₀, …, a_{t-1}]` and `bs = [b₀, …, b_{t-1}]` form the closed alternating walk
`a₀ b₀ a₁ b₁ … a_{t-1} b_{t-1} a₀`. -/
def Cyc (as : List α) (bs : List β) : Prop :=
  ∃ a l, as = a :: l ∧ APath r (as ++ [a]) bs

namespace Cyc

theorem length_eq {as : List α} {bs : List β} (h : Cyc (r := r) as bs) :
    as.length = bs.length := by
  obtain ⟨a, l, rfl, h⟩ := h
  have := h.length_eq
  simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
  omega

theorem rotate_one {as : List α} {bs : List β} (h : Cyc (r := r) as bs) :
    Cyc (r := r) (as.rotate 1) (bs.rotate 1) := by
  obtain ⟨a, l, rfl, h⟩ := h
  cases l with
  | nil =>
    cases h with
    | cons hb hb' h' =>
      cases h' with
      | single => exact ⟨a, [], by simp, by simpa using APath.cons hb hb' (APath.single a)⟩
  | cons a₁ l =>
    cases h with
    | @cons _ _ b _ bs hb hb' h' =>
      refine ⟨a₁, l ++ [a], by simp [List.rotate_cons_succ], ?_⟩
      have h'' : APath r ((a₁ :: l) ++ [a]) bs := by simpa using h'
      have := h''.snoc hb hb'
      simpa [List.rotate_cons_succ] using this

theorem rotate {as : List α} {bs : List β} (h : Cyc (r := r) as bs) (n : ℕ) :
    Cyc (r := r) (as.rotate n) (bs.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have := ih.rotate_one
    rwa [List.rotate_rotate, List.rotate_rotate] at this

/-- Insert `x` (with the new `β`-vertex `y`) between the last `β`-vertex and the first
`α`-vertex. -/
theorem extend_end {a x : α} {l : List α} {bs₀ : List β} {bl y : β}
    (h : Cyc (r := r) (a :: l) (bs₀ ++ [bl])) (h1 : r x bl) (h2 : r x y) (h3 : r a y) :
    Cyc (r := r) (a :: (l ++ [x])) (bs₀ ++ [bl, y]) := by
  obtain ⟨a', l', he, h⟩ := h
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  have h' := h.set_last h1
  have := h'.snoc h2 h3
  exact ⟨a, l ++ [x], rfl, by simpa using this⟩

/-- Replace `a₀ b₀ a₁` by `a₀ y₁ x y₂ a₁`. -/
theorem extend_front {a₀ a₁ x : α} {l : List α} {b₀ y₁ y₂ : β} {bs : List β}
    (h : Cyc (r := r) (a₀ :: a₁ :: l) (b₀ :: bs)) (h1 : r a₀ y₁) (h2 : r x y₁)
    (h3 : r x y₂) (h4 : r a₁ y₂) :
    Cyc (r := r) (a₀ :: x :: a₁ :: l) (y₁ :: y₂ :: bs) := by
  obtain ⟨a', l', he, h⟩ := h
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  cases h with
  | cons _ _ h => exact ⟨a₀, x :: a₁ :: l, rfl, APath.cons h1 h2 (APath.cons h3 h4 h)⟩

/-- The rotation step: the cycle `A₁ A₂` (with `β`-blocks `B₁ B₂`) becomes
`x (A₂ reversed) y A₁ x`. -/
theorem extend_reverse {a₀ c x : α} {A₁ A₂ : List α} {B₁ B₂ : List β} {bj bl y : β}
    (hlen : A₁.length = B₁.length)
    (h : Cyc (r := r) ((a₀ :: A₁) ++ (c :: A₂)) ((B₁ ++ [bj]) ++ (B₂ ++ [bl])))
    (h1 : r x bj) (h2 : r x bl) (h3 : r c y) (h4 : r a₀ y) :
    Cyc (r := r) (x :: ((c :: A₂).reverse ++ (a₀ :: A₁)))
      ((B₂ ++ [bl]).reverse ++ y :: (B₁ ++ [bj])) := by
  obtain ⟨a₀, l', he, h⟩ := h
  simp only [List.cons_append, List.cons.injEq] at he
  obtain ⟨rfl, -⟩ := he
  have h' : APath r ((a₀ :: A₁) ++ c :: (A₂ ++ [a₀])) ((B₁ ++ [bj]) ++ (B₂ ++ [bl])) := by
    simpa using h
  obtain ⟨P₁, P₂⟩ := h'.split_append
  have e1 : ((B₁ ++ [bj]) ++ (B₂ ++ [bl])).take (a₀ :: A₁).length = B₁ ++ [bj] := by
    simp [List.take_append, hlen]
  have e2 : ((B₁ ++ [bj]) ++ (B₂ ++ [bl])).drop (a₀ :: A₁).length = B₂ ++ [bl] := by
    simp [List.drop_append, hlen]
  rw [e1] at P₁
  rw [e2] at P₂
  -- reverse the second block and attach `x` in front of it
  have R := P₂.reverse
  simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append,
    List.cons_append] at R
  have R' := R.set_head h2
  have R'' : APath r ((x :: (A₂.reverse ++ [c]))) (bl :: B₂.reverse) := by simpa using R'
  have R3 := (show APath r ((x :: A₂.reverse) ++ [c]) (bl :: B₂.reverse) by simpa using R'').snoc
    h3 h4
  -- close the first block at `x`
  have P₁' := (show APath r ((a₀ :: A₁) ++ [c]) (B₁ ++ [bj]) by simpa using P₁).set_last h1
  rw [show x :: A₂.reverse ++ [c, a₀] = (x :: A₂.reverse ++ [c]) ++ [a₀] by simp] at R3
  have := R3.append (as₂ := A₁ ++ [x]) (by simpa using P₁')
  refine ⟨x, (c :: A₂).reverse ++ (a₀ :: A₁), rfl, ?_⟩
  simpa using this

end Cyc

variable [DecidableEq α] [DecidableEq β]

/-- A cycle alternating between `X` and `Y`, through the elements of `as` (in `X`) and the
connectors `bs` (in `Y`). -/
structure Good (r : α → β → Prop) (X : Finset α) (Y : Finset β) (as : List α) (bs : List β) :
    Prop where
  cyc : Cyc (r := r) as bs
  two_le : 2 ≤ as.length
  nodup_a : as.Nodup
  nodup_b : bs.Nodup
  sub_a : ∀ a ∈ as, a ∈ X
  sub_b : ∀ b ∈ bs, b ∈ Y

/-- There is a good cycle with one more `X`-vertex than `as`. -/
def Extends (r : α → β → Prop) (X : Finset α) (Y : Finset β) (as : List α) : Prop :=
  ∃ as' bs', Good r X Y as' bs' ∧ as'.length = as.length + 1

variable {X : Finset α} {Y : Finset β}

theorem Good.rotate {as : List α} {bs : List β} (h : Good r X Y as bs) (n : ℕ) :
    Good r X Y (as.rotate n) (bs.rotate n) :=
  ⟨h.cyc.rotate n, by simpa using h.two_le, List.nodup_rotate.2 h.nodup_a,
    List.nodup_rotate.2 h.nodup_b, fun a ha => h.sub_a a (List.mem_rotate.1 ha),
    fun b hb => h.sub_b b (List.mem_rotate.1 hb)⟩

theorem Good.length_eq {as : List α} {bs : List β} (h : Good r X Y as bs) :
    as.length = bs.length := h.cyc.length_eq

omit [DecidableEq α] [DecidableEq β] in
theorem exists_cons_of_length_pos (A : List α) (h : 0 < A.length) :
    ∃ a l, A = a :: l ∧ A[0] = a := by
  cases A with
  | nil => simp at h
  | cons a l => exact ⟨a, l, rfl, rfl⟩

omit [DecidableEq α] [DecidableEq β] in
theorem exists_snoc_of_length_pos (B : List β) (h : 0 < B.length) :
    ∃ B₀ bl, B = B₀ ++ [bl] ∧ B[B.length - 1] = bl := by
  have hB : B ≠ [] := List.ne_nil_of_length_pos h
  exact ⟨B.dropLast, B.getLast hB, (List.dropLast_append_getLast hB).symm,
    (List.getLast_eq_getElem hB).symm⟩

omit [DecidableEq α] [DecidableEq β] in
theorem exists_split_α (A : List α) (j : ℕ) (hj : j + 1 < A.length) :
    ∃ a₀ A₁ c A₂, A = (a₀ :: A₁) ++ (c :: A₂) ∧ A₁.length = j ∧ A[0] = a₀ ∧ A[j + 1] = c := by
  cases A with
  | nil => simp at hj
  | cons a t =>
    simp only [List.length_cons] at hj
    refine ⟨a, t.take j, t[j], t.drop (j + 1), ?_, by simp; omega, rfl, rfl⟩
    rw [List.cons_append, ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]

omit [DecidableEq α] [DecidableEq β] in
theorem exists_split_β (B : List β) (j : ℕ) (hj : j + 1 < B.length) :
    ∃ B₁ bj B₂ bl, B = (B₁ ++ [bj]) ++ (B₂ ++ [bl]) ∧ B₁.length = j ∧ B[j] = bj ∧
      B[B.length - 1] = bl := by
  have hD : B.drop (j + 1) ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  refine ⟨B.take j, B[j], (B.drop (j + 1)).dropLast, (B.drop (j + 1)).getLast hD, ?_,
    by simp; omega, rfl, ?_⟩
  · rw [List.append_assoc, List.dropLast_append_getLast hD, List.singleton_append,
      ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  · rw [List.getLast_eq_getElem hD, List.getElem_drop]
    congr 1
    simp only [List.length_drop]
    omega

/-- Extension at the end of the cycle (Claim 1 after a rotation). -/
theorem Good.extend_end {a : α} {l : List α} {B₀ : List β} {bl : β}
    (hg : Good r X Y (a :: l) (B₀ ++ [bl])) {x : α} (hx : x ∈ X)
    (hxA : x ∉ a :: l) {y : β} (hy : y ∈ Y) (hyB : y ∉ B₀ ++ [bl])
    (h1 : r x bl) (h2 : r x y) (h3 : r a y) : Extends r X Y (a :: l) := by
  have key := hg.cyc.extend_end h1 h2 h3
  have pA : (a :: (l ++ [x])).Perm (x :: a :: l) := by
    simpa using List.perm_append_singleton x (a :: l)
  have pB : (B₀ ++ [bl, y]).Perm (y :: (B₀ ++ [bl])) := by
    simpa using List.perm_append_singleton y (B₀ ++ [bl])
  refine ⟨_, _, ⟨key, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp
  · rw [pA.nodup_iff, List.nodup_cons]; exact ⟨hxA, hg.nodup_a⟩
  · rw [pB.nodup_iff, List.nodup_cons]; exact ⟨hyB, hg.nodup_b⟩
  · intro a' ha
    rw [pA.mem_iff, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hx
    · exact hg.sub_a a' ha
  · intro b hb
    rw [pB.mem_iff, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hy
    · exact hg.sub_b b hb
  · simp

/-- Extension at the front of the cycle (used when `x` has no neighbour on the cycle). -/
theorem Good.extend_front {a₀ a₁ : α} {l : List α} {b₀ : β} {bs : List β}
    (hg : Good r X Y (a₀ :: a₁ :: l) (b₀ :: bs)) {x : α} (hx : x ∈ X)
    (hxA : x ∉ a₀ :: a₁ :: l) {y₁ y₂ : β} (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hy₁B : y₁ ∉ b₀ :: bs) (hy₂B : y₂ ∉ b₀ :: bs) (hne : y₁ ≠ y₂)
    (h1 : r a₀ y₁) (h2 : r x y₁) (h3 : r x y₂) (h4 : r a₁ y₂) :
    Extends r X Y (a₀ :: a₁ :: l) := by
  have key := hg.cyc.extend_front h1 h2 h3 h4
  have pA : (a₀ :: x :: a₁ :: l).Perm (x :: a₀ :: a₁ :: l) := List.Perm.swap x a₀ _
  refine ⟨a₀ :: x :: a₁ :: l, y₁ :: y₂ :: bs, ⟨key, by simp, ?_, ?_, ?_, ?_⟩, by simp⟩
  · rw [pA.nodup_iff, List.nodup_cons]; exact ⟨hxA, hg.nodup_a⟩
  · have hn := hg.nodup_b
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn hy₁B hy₂B ⊢
    exact ⟨⟨hne, hy₁B.2⟩, hy₂B.2, hn.2⟩
  · intro a ha
    rw [pA.mem_iff, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hx
    · exact hg.sub_a a ha
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact hy₁
    · exact hy₂
    · exact hg.sub_b b (List.mem_cons_of_mem _ hb)

/-- The rotation extension (Claim 2 after a rotation). -/
theorem Good.extend_reverse {a₀ c : α} {A₁ A₂ : List α} {B₁ B₂ : List β} {bj bl : β}
    (hlen : A₁.length = B₁.length)
    (hg : Good r X Y ((a₀ :: A₁) ++ (c :: A₂)) ((B₁ ++ [bj]) ++ (B₂ ++ [bl])))
    {x : α} (hx : x ∈ X) (hxA : x ∉ (a₀ :: A₁) ++ (c :: A₂)) {y : β} (hy : y ∈ Y)
    (hyB : y ∉ (B₁ ++ [bj]) ++ (B₂ ++ [bl]))
    (h1 : r x bj) (h2 : r x bl) (h3 : r c y) (h4 : r a₀ y) :
    Extends r X Y ((a₀ :: A₁) ++ (c :: A₂)) := by
  have key := hg.cyc.extend_reverse hlen h1 h2 h3 h4
  have pA : (x :: ((c :: A₂).reverse ++ (a₀ :: A₁))).Perm (x :: ((a₀ :: A₁) ++ (c :: A₂))) :=
    List.Perm.cons x (((List.reverse_perm _).append_right _).trans List.perm_append_comm)
  have pB : ((B₂ ++ [bl]).reverse ++ y :: (B₁ ++ [bj])).Perm
      (y :: ((B₁ ++ [bj]) ++ (B₂ ++ [bl]))) :=
    List.perm_middle.trans
      (List.Perm.cons y (((List.reverse_perm _).append_right _).trans List.perm_append_comm))
  refine ⟨_, _, ⟨key, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [pA.length_eq]; simp
  · rw [pA.nodup_iff, List.nodup_cons]; exact ⟨hxA, hg.nodup_a⟩
  · rw [pB.nodup_iff, List.nodup_cons]; exact ⟨hyB, hg.nodup_b⟩
  · intro a ha
    rw [pA.mem_iff, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hx
    · exact hg.sub_a a ha
  · intro b hb
    rw [pB.mem_iff, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hy
    · exact hg.sub_b b hb
  · rw [pA.length_eq]; simp

omit [DecidableEq α] [DecidableEq β] in
theorem getD_snoc {γ : Type*} (L : List γ) (b d : γ) : (L ++ [b]).getD L.length d = b := by
  simp [List.getD_eq_getElem?_getD]

omit [DecidableEq α] [DecidableEq β] in
theorem getD_rotate {γ : Type*} (l : List γ) (n k : ℕ) (hk : k < l.length) (d : γ) :
    (l.rotate n).getD k d = l.getD ((k + n) % l.length) d := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_rotate,
    List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]

omit [DecidableEq α] [DecidableEq β] in
/-- Index bookkeeping for Claim 2: after rotating so that position `i` comes last,
position `j ≠ i` sits at some `j' < t - 1`. -/
theorem exists_rotated_index {t i j : ℕ} (hi : i < t) (hj : j < t) (hij : i ≠ j) :
    ∃ j', j' + 1 < t ∧ (j' + (i + 1)) % t = j ∧ (j' + 1 + (i + 1)) % t = (j + 1) % t := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i - 1, by omega, ?_, ?_⟩
    · rw [show j - i - 1 + (i + 1) = j by omega, Nat.mod_eq_of_lt hj]
    · rw [show j - i - 1 + 1 + (i + 1) = j + 1 by omega]
  · refine ⟨j + t - i - 1, by omega, ?_, ?_⟩
    · rw [show j + t - i - 1 + (i + 1) = j + t by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · rw [show j + t - i - 1 + 1 + (i + 1) = j + 1 + t by omega, Nat.add_mod_right]

theorem Extends.of_rotate {as : List α} {n : ℕ} (h : Extends r X Y (as.rotate n)) :
    Extends r X Y as := by
  obtain ⟨as', bs', hg, hl⟩ := h
  exact ⟨as', bs', hg, by simpa using hl⟩

/-- Claim 1: if `x` is adjacent to `bᵢ`, the successor `a_{i+1}` of `bᵢ` and `x` have no
common neighbour off the cycle (unless the cycle extends). -/
theorem Good.claim_one {as : List α} {bs : List β} (h : Good r X Y as bs) {x : α}
    (hx : x ∈ X) (hxa : x ∉ as) {y : β} (hy : y ∈ Y) (hyb : y ∉ bs) {i : ℕ}
    (hi : i < bs.length) (da : α) (db : β) (h1 : r x (bs.getD i db)) (h2 : r x y)
    (h3 : r (as.getD ((i + 1) % bs.length) da) y) : Extends r X Y as := by
  have hlen := h.length_eq
  have hg := h.rotate (i + 1)
  obtain ⟨a, l, hA, -⟩ := exists_cons_of_length_pos (as.rotate (i + 1)) (by simp; omega)
  obtain ⟨B₀, bl, hB, -⟩ := exists_snoc_of_length_pos (bs.rotate (i + 1)) (by simp; omega)
  have hB0 : B₀.length = bs.length - 1 := by
    have := congrArg List.length hB; simp at this; omega
  have ea : as.getD ((i + 1) % bs.length) da = a := by
    have := getD_rotate as (i + 1) 0 (by omega) da
    rw [hA] at this
    simp only [List.getD_cons_zero, Nat.zero_add] at this
    rw [this, hlen]
  have eb : bs.getD i db = bl := by
    have := getD_rotate bs (i + 1) B₀.length (by omega) db
    rw [hB] at this
    simp only [List.getD_append_right, le_refl, Nat.sub_self, List.getD_cons_zero] at this
    rw [this, hB0, show bs.length - 1 + (i + 1) = i + bs.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  rw [eb] at h1
  rw [ea] at h3
  rw [hA, hB] at hg
  refine Extends.of_rotate (n := i + 1) ?_
  rw [hA]
  refine hg.extend_end hx ?_ hy ?_ h1 h2 h3
  · rw [← hA, List.mem_rotate]; exact hxa
  · rw [← hB, List.mem_rotate]; exact hyb

/-- Claim 2: the successors of two distinct cycle-neighbours of `x` have no common
neighbour off the cycle (unless the cycle extends). -/
theorem Good.claim_two {as : List α} {bs : List β} (h : Good r X Y as bs) {x : α}
    (hx : x ∈ X) (hxa : x ∉ as) {y : β} (hy : y ∈ Y) (hyb : y ∉ bs) {i j : ℕ}
    (hi : i < bs.length) (hj : j < bs.length) (hij : i ≠ j) (da : α) (db : β)
    (h1 : r x (bs.getD i db)) (h2 : r x (bs.getD j db))
    (h3 : r (as.getD ((i + 1) % bs.length) da) y)
    (h4 : r (as.getD ((j + 1) % bs.length) da) y) : Extends r X Y as := by
  have hlen := h.length_eq
  have hg := h.rotate (i + 1)
  obtain ⟨j', hj't, hj'1, hj'2⟩ := exists_rotated_index hi hj hij
  obtain ⟨a₀, A₁, c, A₂, hA, hA₁, -, -⟩ :=
    exists_split_α (as.rotate (i + 1)) j' (by simp; omega)
  obtain ⟨B₁, bj, B₂, bl, hB, hB₁, -, -⟩ :=
    exists_split_β (bs.rotate (i + 1)) j' (by simp; omega)
  have hBlen : B₂.length + j' + 2 = bs.length := by
    have := congrArg List.length hB; simp at this; omega
  have e0 : as.getD ((i + 1) % bs.length) da = a₀ := by
    have := getD_rotate as (i + 1) 0 (by omega) da
    rw [hA] at this
    simp only [List.cons_append, List.getD_cons_zero, Nat.zero_add] at this
    rw [this, hlen]
  have ec : as.getD ((j + 1) % bs.length) da = c := by
    have := getD_rotate as (i + 1) (j' + 1) (by omega) da
    rw [hA] at this
    simp only [List.cons_append, List.getD_cons_succ, List.getD_append_right, hA₁, le_refl,
      Nat.sub_self, List.getD_cons_zero] at this
    rw [this, hlen, hj'2]
  have ej : bs.getD j db = bj := by
    have := getD_rotate bs (i + 1) j' (by omega) db
    rw [hB] at this
    simp only [List.append_assoc, List.getD_append_right, hB₁, le_refl, Nat.sub_self,
      List.singleton_append, List.getD_cons_zero] at this
    rw [this, hj'1]
  have el : bs.getD i db = bl := by
    have hL : (B₁ ++ [bj] ++ B₂).length = bs.length - 1 := by simp; omega
    have hlast : (bs.rotate (i + 1)).getD (bs.length - 1) db = bl := by
      rw [hB, show B₁ ++ [bj] ++ (B₂ ++ [bl]) = (B₁ ++ [bj] ++ B₂) ++ [bl] by simp, ← hL,
        getD_snoc]
    have := getD_rotate bs (i + 1) (bs.length - 1) (by omega) db
    rw [hlast] at this
    rw [this, show bs.length - 1 + (i + 1) = i + bs.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  rw [el] at h1
  rw [ej] at h2
  rw [e0] at h3
  rw [ec] at h4
  rw [hA, hB] at hg
  refine Extends.of_rotate (n := i + 1) ?_
  rw [hA]
  refine hg.extend_reverse (by rw [hA₁, hB₁]) hx ?_ hy ?_ h2 h1 h4 h3
  · rw [← hA, List.mem_rotate]; exact hxa
  · rw [← hB, List.mem_rotate]; exact hyb

variable [∀ a b, Decidable (r a b)]

omit [DecidableEq α] in
/-- Two vertices of degree `≥ k` into `Y`, with `|Y| ≤ 2k - 2`, share at least two
neighbours. -/
theorem two_le_card_common {k : ℕ} (hY : Y.card + 2 ≤ 2 * k) {u v : α}
    (hu : k ≤ (Y.filter (r u)).card) (hv : k ≤ (Y.filter (r v)).card) :
    2 ≤ ((Y.filter (r u)) ∩ (Y.filter (r v))).card := by
  have h1 := Finset.card_union_add_card_inter (Y.filter (r u)) (Y.filter (r v))
  have h2 := Finset.card_le_card
    (Finset.union_subset (Finset.filter_subset (r u) Y) (Finset.filter_subset (r v) Y))
  omega

/-- The extension step: a good cycle through fewer than `k` vertices of `X` that misses
some `x ∈ X` can be extended. -/
theorem Good.extend {as : List α} {bs : List β} (h : Good r X Y as bs) {k : ℕ}
    (hY : Y.card + 2 ≤ 2 * k) (hdeg : ∀ z ∈ X, k ≤ (Y.filter (r z)).card)
    (hk : as.length + 1 ≤ k) {x : α} (hx : x ∈ X) (hxa : x ∉ as) : Extends r X Y as := by
  by_contra hno
  have hlen := h.length_eq
  have ht2 : 2 ≤ bs.length := by have := h.two_le; omega
  obtain ⟨db, -⟩ : ∃ b, b ∈ bs := List.exists_mem_of_length_pos (by omega)
  set t := bs.length with ht
  set O := Y \ bs.toFinset with hO
  set N : α → Finset β := fun z => O.filter (r z) with hN
  set I := (Finset.range t).filter (fun i => r x (bs.getD i db)) with hI
  set succ : ℕ → α := fun i => as.getD ((i + 1) % t) x with hsucc
  have hbsY : bs.toFinset ⊆ Y := fun b hb => h.sub_b b (List.mem_toFinset.1 hb)
  have hcardbs : bs.toFinset.card = t := List.toFinset_card_of_nodup h.nodup_b
  have hcardO : O.card = Y.card - t := by rw [hO, Finset.card_sdiff_of_subset hbsY, hcardbs]
  have hmemN : ∀ z y, y ∈ N z ↔ (y ∈ Y ∧ y ∉ bs) ∧ r z y := by
    intro z y; simp [hN, hO]
  have hsuccX : ∀ i, succ i ∈ X := by
    intro i
    apply h.sub_a
    simp only [hsucc]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact Nat.mod_lt _ (by omega))]
    exact List.getElem_mem _
  have c1 : ∀ i ∈ I, Disjoint (N x) (N (succ i)) := by
    intro i hi
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [hmemN] at hy1 hy2
    simp only [hI, Finset.mem_filter, Finset.mem_range] at hi
    exact hno (h.claim_one hx hxa hy1.1.1 hy1.1.2 hi.1 x db hi.2 hy1.2 hy2.2)
  have c2 : (I : Set ℕ).PairwiseDisjoint (fun i => N (succ i)) := by
    intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [hmemN] at hy1 hy2
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, hI] at hi hj
    exact hno (h.claim_two hx hxa hy1.1.1 hy1.1.2 hi.1 hj.1 hij x db hi.2 hj.2 hy1.2 hy2.2)
  by_cases hs : I.card = 0
  · -- `x` has no neighbour on the cycle
    have hnb : ∀ b ∈ bs, ¬ r x b := by
      intro b hb hrb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have : i ∈ I := by
        simp only [hI, Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, by rwa [List.getD_eq_getElem _ _ hi]⟩
      rw [Finset.card_eq_zero] at hs
      simp [hs] at this
    obtain ⟨a₀, a₁, l, rfl⟩ : ∃ a₀ a₁ l, as = a₀ :: a₁ :: l := by
      match as, h.two_le with
      | a₀ :: a₁ :: l, _ => exact ⟨a₀, a₁, l, rfl⟩
    obtain ⟨b₀, bs', hbs⟩ : ∃ b₀ bs', bs = b₀ :: bs' := by
      match bs, ht2 with
      | b₀ :: bs', _ => exact ⟨b₀, bs', rfl⟩
    have ha₀ : a₀ ∈ X := h.sub_a _ (by simp)
    have ha₁ : a₁ ∈ X := h.sub_a _ (by simp)
    have hc₀ := two_le_card_common hY (hdeg x hx) (hdeg a₀ ha₀)
    have hc₁ := two_le_card_common hY (hdeg x hx) (hdeg a₁ ha₁)
    obtain ⟨y₁, hy₁⟩ :=
      Finset.card_pos.1 (show 0 < ((Y.filter (r x)) ∩ (Y.filter (r a₀))).card by omega)
    have hc₁' := Finset.pred_card_le_card_erase (s := (Y.filter (r x)) ∩ (Y.filter (r a₁)))
      (a := y₁)
    obtain ⟨y₂, hy₂⟩ :=
      Finset.card_pos.1 (show 0 < (((Y.filter (r x)) ∩ (Y.filter (r a₁))).erase y₁).card by omega)
    simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_filter] at hy₁ hy₂
    rw [hbs] at h hnb
    exact hno (h.extend_front hx hxa hy₁.1.1 hy₂.2.1.1 (fun hm => hnb _ hm hy₁.1.2)
      (fun hm => hnb _ hm hy₂.2.1.2) (Ne.symm hy₂.1) hy₁.2.2 hy₁.1.2 hy₂.2.1.2 hy₂.2.2.2)
  · -- the counting argument
    have hsum : (N x).card + ∑ i ∈ I, (N (succ i)).card ≤ Y.card - t := by
      rw [← Finset.card_biUnion c2,
        ← Finset.card_union_of_disjoint ((Finset.disjoint_biUnion_right _ _ _).2 c1), ← hcardO]
      apply Finset.card_le_card
      apply Finset.union_subset (Finset.filter_subset _ _)
      exact Finset.biUnion_subset.2 (fun i _ => Finset.filter_subset _ _)
    have hdx : k ≤ I.card + (N x).card := by
      have hsub : Y.filter (r x) ⊆ I.image (fun i => bs.getD i db) ∪ N x := by
        intro y hy
        rw [Finset.mem_filter] at hy
        by_cases hyb : y ∈ bs
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hyb
          apply Finset.mem_union_left
          refine Finset.mem_image.2 ⟨i, ?_, List.getD_eq_getElem _ _ hi⟩
          simp only [hI, Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; exact hy.2⟩
        · exact Finset.mem_union_right _ ((hmemN x y).2 ⟨⟨hy.1, hyb⟩, hy.2⟩)
      have := (hdeg x hx).trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
      have := Finset.card_image_le (s := I) (f := fun i => bs.getD i db)
      omega
    have hds : ∀ i ∈ I, k - t ≤ (N (succ i)).card := by
      intro i _
      have hsub : Y.filter (r (succ i)) ⊆ bs.toFinset ∪ N (succ i) := by
        intro y hy
        rw [Finset.mem_filter] at hy
        by_cases hyb : y ∈ bs
        · exact Finset.mem_union_left _ (List.mem_toFinset.2 hyb)
        · exact Finset.mem_union_right _ ((hmemN _ y).2 ⟨⟨hy.1, hyb⟩, hy.2⟩)
      have := (hdeg _ (hsuccX i)).trans
        ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
      omega
    have hsum2 : I.card * (k - t) ≤ ∑ i ∈ I, (N (succ i)).card := by
      have := Finset.sum_le_sum hds
      simpa [Finset.sum_const] using this
    have hprod : (k - t) + (I.card - 1) ≤ I.card * (k - t) := by
      obtain ⟨s', hs'⟩ : ∃ s', I.card = s' + 1 := ⟨I.card - 1, by omega⟩
      rw [hs', Nat.add_sub_cancel, Nat.succ_mul]
      have : s' ≤ s' * (k - t) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have htY : t ≤ Y.card := hcardbs ▸ Finset.card_le_card hbsY
    generalize I.card * (k - t) = P at hsum2 hprod
    omega

/-- **Jackson's theorem** (1981). If `2 ≤ |X| ≤ k`, `|Y| ≤ 2k - 2` and every `x ∈ X` has at
least `k` neighbours in `Y`, there is a cycle alternating between `X` and `Y` through every
vertex of `X`. -/
theorem jackson {k : ℕ} (hX2 : 2 ≤ X.card) (hXk : X.card ≤ k) (hY : Y.card + 2 ≤ 2 * k)
    (hdeg : ∀ z ∈ X, k ≤ (Y.filter (r z)).card) :
    ∃ as bs, Good r X Y as bs ∧ as.toFinset = X := by
  have step : ∀ m, 2 ≤ m → m ≤ X.card → ∃ as bs, Good r X Y as bs ∧ as.length = m := by
    intro m hm2 hmX
    induction m, hm2 using Nat.le_induction with
    | base =>
      obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := Finset.one_lt_card.1 (show 1 < X.card by omega)
      have hc := two_le_card_common hY (hdeg x₀ hx₀) (hdeg x₁ hx₁)
      obtain ⟨y₀, hy₀, y₁, hy₁, hney⟩ :=
        Finset.one_lt_card.1 (show 1 < ((Y.filter (r x₀)) ∩ (Y.filter (r x₁))).card by omega)
      simp only [Finset.mem_inter, Finset.mem_filter] at hy₀ hy₁
      refine ⟨[x₀, x₁], [y₀, y₁], ⟨⟨x₀, [x₁], rfl, ?_⟩, by simp, by simp [hne], by simp [hney],
        ?_, ?_⟩, rfl⟩
      · exact APath.cons hy₀.1.2 hy₀.2.2 (APath.cons hy₁.2.2 hy₁.1.2 (APath.single x₀))
      · intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> assumption
      · intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact hy₀.1.1
        · exact hy₁.1.1
    | succ m hm ih =>
      obtain ⟨as, bs, hg, hl⟩ := ih (by omega)
      obtain ⟨x, hx, hxa⟩ : ∃ x ∈ X, x ∉ as := by
        by_contra hc
        push Not at hc
        have hsub : X ⊆ as.toFinset := fun x hx => List.mem_toFinset.2 (hc x hx)
        have := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hg.nodup_a] at this
        omega
      obtain ⟨as', bs', hg', hl'⟩ := hg.extend hY hdeg (by omega) hx hxa
      exact ⟨as', bs', hg', by omega⟩
  obtain ⟨as, bs, hg, hl⟩ := step X.card hX2 le_rfl
  refine ⟨as, bs, hg, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    exact hg.sub_a a (List.mem_toFinset.1 ha)
  · rw [List.toFinset_card_of_nodup hg.nodup_a, hl]

end ErdosSar.Jackson