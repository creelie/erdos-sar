import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #883: definitions and statements

`coprimeGraph A` is the coprime graph of a finite set `A ⊆ ℕ`: vertices are the
elements of `A`, and distinct `x, y` are adjacent iff `gcd x y = 1`.
-/

namespace ErdosSar

/-- The coprime graph of a finite set of natural numbers. -/
def coprimeGraph (A : Finset ℕ) : SimpleGraph A where
  Adj x y := x ≠ y ∧ Nat.Coprime x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `T n = ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋`, the number of multiples of `2` or `3` in `[1, n]`. -/
def T (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/-- `o n = ⌊n/3⌋ - ⌊n/6⌋`, the number of odd multiples of `3` in `[1, n]`. -/
def o (n : ℕ) : ℕ := n / 3 - n / 6

/-- `E* (n)`: the even numbers in `[1, n]` that are not divisible by `3`. -/
def Estar (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun w => w % 6 = 2 ∨ w % 6 = 4)

/-- `G` contains a cycle with exactly `L` edges (equivalently `L` vertices). -/
def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L

/-- **Erdős Problem #883, Question 1** (Erdős–Sárközy). For all large `n`, every
`A ⊆ [1, n]` with `|A| > T n` has a coprime graph containing every odd cycle of
length at most `n/3 + 1`. (For integer `L`, `L ≤ n/3 + 1` is `L - 1 ≤ ⌊n/3⌋`.)

This is an open problem; it is only *stated* here, not proved. -/
def Question1 : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → T n < A.card →
    ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ n / 3 + 1 → HasCycleOfLength (coprimeGraph A) L

/-- The main theorem of the accompanying paper (Theorem 1.1): Question 1 holds for
sets `A` that omit at most `n/70` elements of `E* (n)`, and in fact all cycle lengths
`2l+1` with `1 ≤ l ≤ o n` occur. Proved in `ErdosSar.paperTheorem_holds`. -/
def PaperTheorem : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → T n < A.card →
    70 * (Estar n \ A).card ≤ n →
    ∀ l : ℕ, 1 ≤ l → l ≤ o n → HasCycleOfLength (coprimeGraph A) (2 * l + 1)

end ErdosSar
