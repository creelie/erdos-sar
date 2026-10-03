# Erdős Problem #883 (Erdős–Sárközy): odd cycles in coprime graphs

For `A ⊆ {1,…,n}` let `G(A)` be the coprime graph of `A` (distinct `x, y` are adjacent iff
`gcd(x, y) = 1`), and let `T(n) = ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋`.

**Question 1** ([erdosproblems.com/883](https://www.erdosproblems.com/883)). If `n` is large and
`|A| > T(n)`, does `G(A)` contain every odd cycle of length at most `n/3 + 1`?

## Status: what is and is not proved

| Statement | Where | Status |
|---|---|---|
| Question 1 in full | `ErdosSar.Question1` | **Open.** Only stated in Lean, not proved. |
| Paper's Theorem 1.1: Question 1 when `A` omits at most `n/70` of the numbers `≡ 2, 4 (mod 6)` | `paper/`, `ErdosSar.PaperTheorem` | Proved on paper, using Jackson (1981) and Erdős–Sárközy (1997). **Not formalized**: stated in Lean only. |
| Theorem 1.1 implies Question 1 for every such `A` | `ErdosSar.question1_of_paperTheorem` | Lean-verified |
| `T(n)` is sharp: the multiples of 2 or 3 have exactly `T(n)` elements and no triangle | `ErdosSar.card_M23`, `ErdosSar.not_hasCycle3_M23` | Lean-verified |
| The length `2·o(n)+1` is sharp: an odd cycle of length `L` in `G(A)` satisfies `L + 1 ≤ 2·#{odd elements of A}` | `ErdosSar.odd_cycle_length_bound` | Lean-verified |
| Coprime-pair lemma (paper Lemma 2.7): `o(n)+1` odd numbers in `[1, n]`, `n ≥ 13`, contain a coprime pair | `ErdosSar.coprime_pair` | Lean-verified |
| Moment-bound constants of paper Lemma 2.4 (`≤ 5.82·10⁻⁴`, `≤ 3.09·10⁻⁴`) | `verification/constants_interval.py` | Certified with outward-rounded interval arithmetic (not in Lean) |

"Lean-verified" means the theorem builds with Lean 4 and Mathlib, with no `sorry`, and
`#print axioms` (see `scripts/Axioms.lean`) reports only `propext`, `Classical.choice`
and `Quot.sound`. CI re-checks this on every push.

### What remains for an unconditional, formal resolution

1. **Mathematics, open:** the case in which `A` omits more than `n/70` of the numbers
   `≡ 2, 4 (mod 6)` (paper, Section 7; exploratory, non-rigorous scripts in
   `code/caseB_exploration`).
2. **Formalization of Theorem 1.1:** Jackson's theorem on long cycles in bipartite graphs,
   the inclusion–exclusion count of paper Lemma 2.3, the moment bound of Lemma 2.4 together
   with its numerical constants, and the cycle assembly of Sections 3–4. The Erdős–Sárközy
   theorem is only needed for the cycle lengths 3, 5, 7, 9 and can be replaced by a direct
   greedy argument.

## Layout

- `ErdosSar/Defs.lean`: coprime graph, `T`, `o`, `E*`, statements `Question1` and `PaperTheorem`.
- `ErdosSar/Extremal.lean`: sharpness of the threshold `T(n)` and of the cycle length.
- `ErdosSar/CoprimePair.lean`: paper Lemma 2.7.
- `ErdosSar/Statements.lean`: Theorem 1.1 implies the restricted Question 1.
- `paper/`: the paper (LaTeX source and PDF).
- `code/`: the scripts that accompany the paper.
- `verification/constants_interval.py`: rigorous recheck of the Lemma 2.4 constants.

## Building

```
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean scripts/Axioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1`, Mathlib `v4.34.1`.

To recheck the constants: `pip install mpmath sympy && python3 verification/constants_interval.py`.
