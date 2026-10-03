import ErdosSar.Defs
import ErdosSar.Jackson
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# From lists to cycles, and the assembly of disjoint paths through Jackson's theorem

* `hasCycle_of_list`: a duplicate-free list `x :: l` of elements of `A`, with consecutive
  entries coprime and the last entry coprime to `x`, gives a cycle of length `|l| + 1` in the
  coprime graph of `A`.
* `assembly`: given pairwise disjoint coprime paths `ex c` (`c ∈ X`) and a pool `B` of further
  elements of `A`, such that the bipartite graph between the paths and `B` (a path is joined to
  `β` when `β` is coprime to both of its ends) satisfies the hypotheses of Jackson's theorem,
  the coprime graph contains a cycle of length `∑_{c ∈ X} |ex c| + |X|`.
-/

namespace ErdosSar

open Finset

theorem isChain_ne_of_nodup {α : Type*} {R : α → α → Prop} {L : List α} (hnd : L.Nodup)
    (hc : L.IsChain R) : L.IsChain (fun a b => a ≠ b ∧ R a b) := by
  induction hc with
  | nil => exact .nil
  | singleton a => exact .singleton a
  | cons_cons hr h ih =>
    rename_i a b l
    have hnd' := List.nodup_cons.1 hnd
    refine .cons_cons ⟨fun hab => hnd'.1 (by rw [hab]; exact List.mem_cons_self), hr⟩ (ih hnd'.2)

theorem exists_walk_support {V : Type*} (G : SimpleGraph V) :
    ∀ (a : V) (l : List V), (a :: l).IsChain G.Adj →
      ∃ p : G.Walk a ((a :: l).getLast (List.cons_ne_nil a l)), p.support = a :: l
  | a, [], _ => ⟨SimpleGraph.Walk.nil, rfl⟩
  | a, b :: l, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨p, hp⟩ := exists_walk_support G b l h.2
    exact ⟨SimpleGraph.Walk.cons h.1 p, by simp [hp]⟩

theorem exists_cycle_of_list {V : Type*} (G : SimpleGraph V) (x : V) (l : List V)
    (hnd : (x :: l).Nodup) (h2 : 2 ≤ l.length) (hc : (x :: l ++ [x]).IsChain G.Adj) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = l.length + 1 := by
  obtain ⟨y, l', rfl⟩ : ∃ y l', l = y :: l' := by
    cases l with
    | nil => simp at h2
    | cons y l' => exact ⟨y, l', rfl⟩
  have hc' : (x :: y :: (l' ++ [x])).IsChain G.Adj := by simpa using hc
  rw [List.isChain_cons_cons] at hc'
  obtain ⟨q, hq⟩ := exists_walk_support G y (l' ++ [x]) hc'.2
  have hlast : (y :: (l' ++ [x])).getLast (List.cons_ne_nil _ _) = x := by
    simp
  let q' := q.copy rfl hlast
  refine ⟨x, SimpleGraph.Walk.cons hc'.1 q', ?_, ?_⟩
  · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def,
        SimpleGraph.Walk.support_tail_of_not_nil _ SimpleGraph.Walk.not_nil_cons,
        SimpleGraph.Walk.support_cons, List.tail_cons]
      simp only [q', SimpleGraph.Walk.support_copy, hq]
      have : (y :: (l' ++ [x])).Perm (x :: y :: l') := by
        rw [← List.cons_append]
        exact List.perm_append_singleton x (y :: l') |>.trans (List.Perm.refl _)
      exact this.nodup_iff.2 hnd
    · simp only [SimpleGraph.Walk.length_cons, q', SimpleGraph.Walk.length_copy]
      have := q.length_support
      rw [hq] at this
      simp at this h2 ⊢
      omega
  · simp only [SimpleGraph.Walk.length_cons, q', SimpleGraph.Walk.length_copy]
    have := q.length_support
    rw [hq] at this
    simp at this ⊢
    omega

theorem mem_of_mem_getLast? {L : List ℕ} {a : ℕ} (h : a ∈ L.getLast?) : a ∈ L :=
  List.mem_of_getLast? h

/-- A duplicate-free cyclic coprime list gives a cycle in the coprime graph. -/
theorem hasCycle_of_list (A : Finset ℕ) (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup)
    (h2 : 2 ≤ l.length) (hA : ∀ v ∈ x :: l, v ∈ A)
    (hc : (x :: l ++ [x]).IsChain Nat.Coprime) :
    HasCycleOfLength (coprimeGraph A) (l.length + 1) := by
  classical
  have hxA : x ∈ A := hA x List.mem_cons_self
  let f : ℕ → A := fun v => if h : v ∈ A then ⟨v, h⟩ else ⟨x, hxA⟩
  have hf : ∀ v (h : v ∈ A), f v = ⟨v, h⟩ := fun v h => by simp [f, h]
  have hne : (x :: l ++ [x]).IsChain (fun a b => a ≠ b ∧ Nat.Coprime a b) := by
    obtain ⟨c1, -, c3⟩ := List.isChain_append.1 hc
    refine List.isChain_append.2 ⟨isChain_ne_of_nodup hnd c1, .singleton x, ?_⟩
    intro a ha b hb
    refine ⟨?_, c3 a ha b hb⟩
    have hb' : b = x := (by simpa using hb : x = b).symm
    subst hb'
    obtain ⟨y, l', rfl⟩ : ∃ y l', l = y :: l' := by
      cases l with
      | nil => simp at h2
      | cons y l' => exact ⟨y, l', rfl⟩
    have ha' : a ∈ y :: l' := by
      rw [List.getLast?_cons_cons] at ha
      exact List.mem_of_getLast? ha
    intro hab; subst hab
    exact (List.nodup_cons.1 hnd).1 ha'
  have hmem : ∀ v ∈ x :: l ++ [x], v ∈ A := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · exact hA v h
    · rw [List.mem_singleton.1 h]; exact hxA
  have hchain : ((x :: l ++ [x]).map f).IsChain (coprimeGraph A).Adj := by
    rw [List.isChain_map]
    refine hne.imp_of_mem_imp ?_
    intro a b ha hb hab
    rw [hf a (hmem a ha), hf b (hmem b hb)]
    exact ⟨fun h => hab.1 (congrArg Subtype.val h), hab.2⟩
  have hnd' : (f x :: l.map f).Nodup := by
    rw [← List.map_cons]
    refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    rw [hf a (hA a ha), hf b (hA b hb)] at hab
    exact congrArg Subtype.val hab
  obtain ⟨v, p, hp, hlen⟩ := exists_cycle_of_list (coprimeGraph A) (f x) (l.map f) hnd'
    (by simpa using h2) (by simpa using hchain)
  exact ⟨v, p, hp, by simpa using hlen⟩

/-! ## Concatenating paths along a Jackson cycle -/

/-- `cycList ex [a₀, …, a_{t-1}] [b₀, …, b_{t-1}] = ex a₀ ++ [b₀] ++ ⋯ ++ ex a_{t-1} ++ [b_{t-1}]`. -/
def cycList (ex : ℕ → List ℕ) : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => ex a ++ b :: cycList ex as bs
  | _, _ => []

variable (ex : ℕ → List ℕ)

@[simp] theorem cycList_cons_cons (a b : ℕ) (as bs : List ℕ) :
    cycList ex (a :: as) (b :: bs) = ex a ++ b :: cycList ex as bs := rfl

@[simp] theorem cycList_nil_left (bs : List ℕ) : cycList ex [] bs = [] := rfl

@[simp] theorem cycList_nil_right (as : List ℕ) : cycList ex as [] = [] := by
  cases as <;> rfl

theorem cycList_append_single :
    ∀ (as bs : List ℕ) (a : ℕ), as.length = bs.length → cycList ex (as ++ [a]) bs = cycList ex as bs
  | [], [], _, _ => rfl
  | _ :: as, _ :: bs, a, h => by
    simp only [List.cons_append, cycList_cons_cons]
    rw [cycList_append_single as bs a (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem mem_cycList : ∀ {as bs : List ℕ} {v : ℕ}, v ∈ cycList ex as bs →
    (∃ c ∈ as, v ∈ ex c) ∨ v ∈ bs
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, v, h => by
    simp only [cycList_cons_cons, List.mem_append, List.mem_cons] at h
    rcases h with h | rfl | h
    · exact Or.inl ⟨a, List.mem_cons_self, h⟩
    · exact Or.inr List.mem_cons_self
    · rcases mem_cycList h with ⟨c, hc, hv⟩ | hv
      · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hv⟩
      · exact Or.inr (List.mem_cons_of_mem _ hv)

theorem length_cycList : ∀ (as bs : List ℕ), as.length = bs.length →
    (cycList ex as bs).length = (as.map (fun c => (ex c).length + 1)).sum
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [cycList_cons_cons, List.length_append, List.length_cons, List.map_cons,
      List.sum_cons]
    rw [length_cycList as bs (by simpa using h)]
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem nodup_cycList : ∀ (as bs : List ℕ), as.Nodup → bs.Nodup →
    (∀ c ∈ as, (ex c).Nodup) →
    (∀ c ∈ as, ∀ c' ∈ as, c ≠ c' → (ex c).Disjoint (ex c')) →
    (∀ c ∈ as, ∀ b ∈ bs, b ∉ ex c) → (cycList ex as bs).Nodup
  | [], _, _, _, _, _, _ => by simp
  | _ :: _, [], _, _, _, _, _ => by simp
  | a :: as, b :: bs, ha, hb, hnd, hdisj, hB => by
    simp only [cycList_cons_cons]
    have ha' := List.nodup_cons.1 ha
    have hb' := List.nodup_cons.1 hb
    have ih := nodup_cycList as bs ha'.2 hb'.2
      (fun c hc => hnd c (List.mem_cons_of_mem _ hc))
      (fun c hc c' hc' h => hdisj c (List.mem_cons_of_mem _ hc) c' (List.mem_cons_of_mem _ hc') h)
      (fun c hc b' hb'' => hB c (List.mem_cons_of_mem _ hc) b' (List.mem_cons_of_mem _ hb''))
    rw [List.nodup_append]
    refine ⟨hnd a List.mem_cons_self, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨fun hbm => ?_, ih⟩
      rcases mem_cycList ex hbm with ⟨c, hc, hv⟩ | hv
      · exact hB c (List.mem_cons_of_mem _ hc) b List.mem_cons_self hv
      · exact hb'.1 hv
    · intro v hv w hw hvw
      subst hvw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hB a List.mem_cons_self v List.mem_cons_self hv
      · rcases mem_cycList ex hw with ⟨c, hc, hv'⟩ | hv'
        · have hac : a ≠ c := fun h => ha'.1 (h ▸ hc)
          exact hdisj a List.mem_cons_self c (List.mem_cons_of_mem _ hc) hac hv hv'
        · exact hB a List.mem_cons_self v (List.mem_cons_of_mem _ hv') hv

theorem getLast?_eq_getLastD {L : List ℕ} (h : L ≠ []) : L.getLast? = some (L.getLastD 0) := by
  rw [List.getLastD_eq_getLast?]
  cases hL : L.getLast? with
  | none => simp at hL; exact absurd hL h
  | some a => rfl

theorem head?_eq_headD {L : List ℕ} (h : L ≠ []) : L.head? = some (L.headD 0) := by
  cases L with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- The relation used for Jackson's theorem: `β` is coprime to both ends of `ex c`. -/
def EndRel (c β : ℕ) : Prop :=
  Nat.Coprime ((ex c).getLastD 0) β ∧ Nat.Coprime β ((ex c).headD 0)

instance (c β : ℕ) : Decidable (EndRel ex c β) := by unfold EndRel; infer_instance

theorem chain_of_apath {as bs : List ℕ} (h : Jackson.APath (EndRel ex) as bs)
    (hne : ∀ c ∈ as, ex c ≠ []) (hch : ∀ c ∈ as, (ex c).IsChain Nat.Coprime) :
    (cycList ex as bs ++ ex (as.getLastD 0)).IsChain Nat.Coprime ∧
      (cycList ex as bs ++ ex (as.getLastD 0)).head? = (ex (as.headD 0)).head? := by
  induction h with
  | single a =>
    exact ⟨hch a List.mem_cons_self, rfl⟩
  | cons hab ha'b hp ih =>
    rename_i a a' b as bs
    have ih' := ih (fun c hc => hne c (List.mem_cons_of_mem _ hc))
      (fun c hc => hch c (List.mem_cons_of_mem _ hc))
    have hlast : (a :: a' :: as).getLastD 0 = (a' :: as).getLastD 0 := rfl
    rw [hlast, cycList_cons_cons, List.append_assoc, List.cons_append]
    set rest := cycList ex (a' :: as) bs ++ ex ((a' :: as).getLastD 0)
    have hnea := hne a List.mem_cons_self
    have hnea' := hne a' (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨?_, ?_⟩
    · refine List.isChain_append.2 ⟨hch a List.mem_cons_self, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, ih'.1⟩
        intro y hy
        rw [ih'.2, List.headD_cons, head?_eq_headD hnea'] at hy
        cases hy
        exact ha'b.2
      · intro x hx y hy
        rw [getLast?_eq_getLastD hnea] at hx
        cases hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact hab.1
    · rw [List.head?_append_of_ne_nil _ hnea]
      rfl

theorem sum_map_succ (f : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map (fun c => f c + 1)).sum = (l.map f).sum + l.length
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [sum_map_succ f l]; omega

/-- **Assembly of disjoint paths through Jackson's theorem.** -/
theorem assembly (A X B : Finset ℕ) (k : ℕ)
    (hne : ∀ c ∈ X, ex c ≠ []) (hch : ∀ c ∈ X, (ex c).IsChain Nat.Coprime)
    (hnd : ∀ c ∈ X, (ex c).Nodup)
    (hdisj : ∀ c ∈ X, ∀ c' ∈ X, c ≠ c' → (ex c).Disjoint (ex c'))
    (hexB : ∀ c ∈ X, ∀ v ∈ ex c, v ∉ B)
    (hexA : ∀ c ∈ X, ∀ v ∈ ex c, v ∈ A) (hBA : B ⊆ A)
    (hX2 : 2 ≤ X.card) (hXk : X.card ≤ k) (hBk : B.card + 2 ≤ 2 * k)
    (hdeg : ∀ c ∈ X, k ≤ (B.filter (fun β => EndRel ex c β)).card) :
    HasCycleOfLength (coprimeGraph A) (∑ c ∈ X, (ex c).length + X.card) := by
  classical
  obtain ⟨as, bs, hg, hX⟩ := Jackson.jackson (r := EndRel ex) hX2 hXk hBk hdeg
  have hlen : as.length = bs.length := hg.cyc.length_eq
  have hasX : ∀ c ∈ as, c ∈ X := hg.sub_a
  obtain ⟨a₀, l, has, hpath⟩ := hg.cyc
  -- the closed chain
  have hch1 := (chain_of_apath ex hpath
    (fun c hc => hne c (by
      rcases List.mem_append.1 hc with h | h
      · exact hasX c h
      · rw [List.mem_singleton.1 h]; exact hasX a₀ (by rw [has]; exact List.mem_cons_self)))
    (fun c hc => hch c (by
      rcases List.mem_append.1 hc with h | h
      · exact hasX c h
      · rw [List.mem_singleton.1 h]; exact hasX a₀ (by rw [has]; exact List.mem_cons_self)))).1
  rw [cycList_append_single ex as bs a₀ hlen, List.getLastD_concat] at hch1
  have ha₀X : a₀ ∈ X := hasX a₀ (by rw [has]; exact List.mem_cons_self)
  obtain ⟨h₀, t₀, ht₀⟩ : ∃ h₀ t₀, ex a₀ = h₀ :: t₀ := by
    cases h : ex a₀ with
    | nil => exact absurd h (hne a₀ ha₀X)
    | cons h₀ t₀ => exact ⟨h₀, t₀, rfl⟩
  obtain ⟨b₀, bs', hbs⟩ : ∃ b₀ bs', bs = b₀ :: bs' := by
    cases bs with
    | nil => rw [has] at hlen; simp at hlen
    | cons b₀ bs' => exact ⟨b₀, bs', rfl⟩
  set F := cycList ex as bs with hF
  have hFeq : F = h₀ :: (t₀ ++ b₀ :: cycList ex l bs') := by
    rw [hF, has, hbs, cycList_cons_cons, ht₀]; rfl
  have hclosed : (h₀ :: (t₀ ++ b₀ :: cycList ex l bs') ++ [h₀]).IsChain Nat.Coprime := by
    rw [ht₀] at hch1
    rw [← hFeq]
    have : F ++ h₀ :: t₀ = (F ++ [h₀]) ++ t₀ := by simp
    rw [this] at hch1
    exact hch1.left_of_append
  -- nodup
  have hFnd : F.Nodup :=
    nodup_cycList ex as bs hg.nodup_a hg.nodup_b (fun c hc => hnd c (hasX c hc))
      (fun c hc c' hc' h => hdisj c (hasX c hc) c' (hasX c' hc') h)
      (fun c hc b hb hbex => hexB c (hasX c hc) b hbex (hg.sub_b b hb))
  -- membership in `A`
  have hFA : ∀ v ∈ F, v ∈ A := by
    intro v hv
    rcases mem_cycList ex hv with ⟨c, hc, hv'⟩ | hv'
    · exact hexA c (hasX c hc) v hv'
    · exact hBA (hg.sub_b v hv')
  -- length
  have hFlen : F.length = ∑ c ∈ X, (ex c).length + X.card := by
    rw [hF, length_cycList ex as bs hlen, ← hX, List.sum_toFinset _ hg.nodup_a,
      List.toFinset_card_of_nodup hg.nodup_a, sum_map_succ]
  have hXlen : X.card ≤ as.length := by
    rw [← hX]; exact List.toFinset_card_le as
  have hge : 2 * X.card ≤ F.length := by
    rw [hFlen]
    have : X.card ≤ ∑ c ∈ X, (ex c).length := by
      calc X.card = ∑ c ∈ X, 1 := by simp
        _ ≤ ∑ c ∈ X, (ex c).length := Finset.sum_le_sum fun c hc => by
            have := hne c hc
            cases h : ex c with
            | nil => exact absurd h this
            | cons _ _ => simp
    omega
  have hLlen : (t₀ ++ b₀ :: cycList ex l bs').length + 1 = F.length := by rw [hFeq]; simp
  have hFnd' : (h₀ :: (t₀ ++ b₀ :: cycList ex l bs')).Nodup := by rw [← hFeq]; exact hFnd
  have hFA' : ∀ v ∈ h₀ :: (t₀ ++ b₀ :: cycList ex l bs'), v ∈ A := by rw [← hFeq]; exact hFA
  have hcyc := hasCycle_of_list A h₀ (t₀ ++ b₀ :: cycList ex l bs') hFnd' (by omega) hFA'
    hclosed
  rw [← hFlen, ← hLlen]
  exact hcyc

end ErdosSar
