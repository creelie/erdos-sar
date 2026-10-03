# Erdős Problem #883 (Erdős–Sárközy): odd cycles in coprime graphs

For `A ⊆ {1,…,n}` let `G(A)` be the coprime graph of `A` (distinct `x, y` are adjacent iff
`gcd(x, y) = 1`), and let `T(n) = ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋`.

**Question 1** ([erdosproblems.com/883](https://www.erdosproblems.com/883)). If `n` is large and
`|A| > T(n)`, does `G(A)` contain every odd cycle of length at most `n/3 + 1`?

## Status: what is and is not proved

| Statement | Lean name | Status |
|---|---|---|
| Question 1 in full | `ErdosSar.Question1` | **Open.** Stated in Lean, not proved. |
| **Theorem 1.1**: for `n ≥ N₀ = 1000·23·2²²`, if `A ⊆ [1, n]`, `|A| > T(n)` and `A` omits at most `n/70` of the numbers `≡ 2, 4 (mod 6)` in `[1, n]`, then `G(A)` has a cycle of length `2l+1` for every `1 ≤ l ≤ o(n)` | `ErdosSar.paperTheorem_holds` | **Lean-verified** |
| Question 1 for every `A` omitting at most `n/70` of the numbers `≡ 2, 4 (mod 6)` | `ErdosSar.question1_restricted` | **Lean-verified** |
| Triangles: every `A ⊆ [1, n]` with `n ≥ 13` and `|A| > T(n)` (no other condition) has a triangle | `ErdosSar.triangle` | **Lean-verified** |
| `T(n)` is sharp: the multiples of 2 or 3 have `T(n)` elements and no triangle | `ErdosSar.card_M23`, `ErdosSar.not_hasCycle3_M23` | Lean-verified |
| The length `2·o(n)+1` is sharp: an odd cycle of length `L` in `G(A)` has `L + 1 ≤ 2·#{odd elements of A}` | `ErdosSar.odd_cycle_length_bound` | Lean-verified |

"Lean-verified" means the theorem builds with Lean 4 and Mathlib, with no `sorry`, and
`#print axioms` (see `scripts/Axioms.lean`) reports only `propext`, `Classical.choice`
and `Quot.sound`. CI re-checks this on every push.

### Ingredients, all formalized here

- **Jackson's theorem** (J. Combin. Theory Ser. B 30, 1981), `ErdosSar.Jackson.jackson`, with a new short
  proof (maximal cycle plus a counting argument; see the file header).
- **Counting lemma**, `ErdosSar.abs_card_Nstar_sub_le`: `|#N*(n, m) − (n/3)ρ'(m)| ≤ 2^{ω'(m)} − 1/3`,
  by induction on the prime set.
- **Moment bound** (Rankin's trick), `ErdosSar.card_phiT_le`, with constants certified exactly:
  the Euler product over primes below 200 is a rational number compared by the kernel
  (`decide +kernel`, file `ErdosSar/Numerics.lean`), and the tail uses `g_m(p) ≤ 2m/p` and
  `∑_{p ≥ 200} 1/p² ≤ 1/199`. Consequences: `#{z ≤ n : ρ'(z) ≤ x} ≤ xn/560` for `x ≤ 14/25`
  (`ErdosSar.card_rho_le`) and at most `n/1000` integers have `∏_{p | z, p ≥ 11}(1 − 1/p) ≤ 3/4`.
- **No analytic number theory beyond this**: `ω'(m)` is controlled by `(ω'(m)+1)! ≤ m`
  (`ErdosSar.large_n`), so neither Robin's bound nor Rosser–Schoenfeld is needed, and the
  threshold `N₀` is explicit.
- **No Erdős–Sárközy**: triangles come from a block argument valid for every `A`, cycles of
  length 5 and 7 are built directly (`ErdosSar.cycle_five`, `ErdosSar.cycle_seven`), and all
  lengths from 9 on come from Jackson's theorem applied to the paths through hard numbers
  (`ErdosSar.long_cycle`, `ErdosSar.assembly`).

### What remains for Question 1

The case in which `A` omits more than `n/70` of the numbers `≡ 2, 4 (mod 6)` (paper,
Section 7) is open mathematics; no proof of it exists here.

## Layout

- `ErdosSar/Defs.lean`: coprime graph, `T`, `o`, `E*`, statements `Question1` and `PaperTheorem`.
- `ErdosSar/Extremal.lean`: sharpness of the threshold `T(n)` and of the cycle length.
- `ErdosSar/CoprimePair.lean`: a coprime pair among `o(n)+1` odd numbers.
- `ErdosSar/Jackson.lean`: Jackson's theorem on cycles in bipartite graphs.
- `ErdosSar/Counting.lean`, `ErdosSar/Rho.lean`: counting in `E*(n)`, the density `ρ'`.
- `ErdosSar/Moment.lean`, `ErdosSar/Numerics.lean`, `ErdosSar/HardCount.lean`: the moment bound and its constants.
- `ErdosSar/LargeN.lean`, `ErdosSar/OddCount.lean`, `ErdosSar/Greedy.lean`, `ErdosSar/Setup.lean`: auxiliary estimates.
- `ErdosSar/Assembly.lean`: from lists to cycles; joining disjoint paths through Jackson's theorem.
- `ErdosSar/Triangle.lean`, `ErdosSar/Short.lean`, `ErdosSar/LongCycle.lean`: the cycles.
- `ErdosSar/Main.lean`: Theorem 1.1 (`paperTheorem_holds`) and the restricted Question 1.
- `paper/`: the paper (LaTeX source and PDF).
- `code/`: the scripts that accompany the paper.
- `verification/constants_interval.py`: interval-arithmetic recheck of the paper's floating-point constants.

## Building

```
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean scripts/Axioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1`, Mathlib `v4.34.1`.

To recheck the constants: `pip install mpmath sympy && python3 verification/constants_interval.py`.
