# Erdős Problem #883: odd cycles in coprime graphs

For a finite set `A` of positive integers, the coprime graph `G(A)` has vertex set `A`, two
distinct elements being adjacent when they are coprime. Let
`T(n) = ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋`, the number of multiples of 2 or 3 in `[1, n]`.

**Question 1** (Erdős and Sárközy, [Electron. J. Combin. 4 (1997) R8](https://doi.org/10.37236/1323);
[erdosproblems.com/883](https://www.erdosproblems.com/883)). For large `n`, if `A ⊆ [1, n]` and
`|A| > T(n)`, does `G(A)` contain a cycle of every odd length from 3 to `n/3 + 1`?

**Answer: yes.** This repository proves it in Lean 4 with Mathlib:

```lean
theorem ErdosSar.question1 : ErdosSar.Question1

def Question1 : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → T n < A.card →
    ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ n / 3 + 1 → HasCycleOfLength (coprimeGraph A) L
```

`#print axioms ErdosSar.question1` reports only `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry` and no `native_decide`; every numerical inequality is checked by the kernel
(`decide +kernel`) or by `norm_num`. CI rebuilds the project and prints the axioms on every push.

The statement is for `n ≥ n₀`, as in Erdős and Sárközy's formulation; small `n` are not treated.
The threshold `n₀` is the largest of `N₁ = 10⁶·30·2²⁹` and the thresholds of the sixteen density
certificates. The certificate thresholds are finite but not computed explicitly.

## Results proved

| Paper | Statement | Lean |
|---|---|---|
| Theorem 1.1 | Question 1 | `question1` |
| Theorem 5.1 | `n ≥ 13`, `\|A\| > T(n)` gives a triangle | `triangle` |
| Theorem 6.1 | `n ≥ N₀ = 1000·23·2²²`, `\|A\| > T(n)`, and `A` misses at most `n/70` of the numbers `≡ 2, 4 (mod 6)`: a cycle of length `2l+1` for every `1 ≤ l ≤ o(n)` | `paperTheorem_holds`, `question1_restricted` |
| Proposition 7.2 | unit construction | `t_cycle` |
| Proposition 7.3 | giant-path construction | `gp_cycle` |
| Theorem 3.1 | Jackson's theorem on cycles in bipartite graphs | `Jackson.jackson` |
| Section 1 | `T(n)` is sharp; odd cycles need `(L+1)/2` odd vertices | `card_M23`, `not_hasCycle3_M23`, `odd_cycle_length_bound` |

## How the proof goes

Let `d` be the number of integers `≡ 2, 4 (mod 6)` in `[1, n]` missing from `A`.

- `l = 1`: a block argument gives a triangle for every `A` (`Triangle.lean`).
- `70d ≤ n`: short paths through odd elements of `A` are joined into one cycle by Jackson's
  theorem, with the even numbers prime to 3 as connectors (`LongCycle.lean`, `Main.lean`).
- `70d > n`: either all multiples of 2 or 3 in `A` connect units of `A` (`SchemeT.lean`), or one
  long path alternating between units and multiples of 6 absorbs the vertices the connectors
  cannot carry (`GPPath.lean`, `SchemeGP.lean`). Both need many elements `z` with large
  `ρ'(z) = ∏_{p | z, p ≥ 5} (1 − 1/p)`; the exceptions are bounded by sixteen certificates
  (`Cert.lean`, `Certs.lean`) built from Rankin's moment method with constants checked in exact
  rational arithmetic. Three intervals of `μ_T/n` and 29 boxes of `(3d/n, μ₆/n)` cover all cases
  (`Boxes.lean`, `Closure.lean`).

No result from analytic number theory is assumed: the number of prime factors is controlled by
`(ω'(m)+1)! ≤ m`, and the Euler products by an explicit tail bound.

## Layout

- `ErdosSar/`: the Lean development (28 files).
  - `Defs.lean`, `Statements.lean`: definitions, `Question1`, `PaperTheorem` (Theorem 6.1).
  - `Extremal.lean`: sharpness examples.
  - `CoprimePair.lean`, `Greedy.lean`, `OddCount.lean`, `LargeN.lean`: combinatorial and size lemmas.
  - `Counting.lean`, `CountingR.lean`, `Rho.lean`: counting in residue classes, the density `ρ'`.
  - `Moment.lean`, `Numerics.lean`, `HardCount.lean`: the moment bound and its constants.
  - `Jackson.lean`, `Assembly.lean`: Jackson's theorem and the assembly of paths into a cycle.
  - `Triangle.lean`, `Short.lean`, `Setup.lean`, `LongCycle.lean`, `Main.lean`: Theorems 5.1 and 6.1.
  - `Cert.lean`, `Certs.lean`: the density certificates.
  - `OpenSetup.lean`, `GPPath.lean`, `SchemeGP.lean`, `SchemeT.lean`: the two constructions.
  - `Boxes.lean`, `Closure.lean`: the case analysis and `question1`.
- `scripts/Axioms.lean`: prints the axioms of the main theorems (run by CI).
- `verification/open_case/`: the box data, the search that found it, and the generator of
  `Closure.lean`.
- `code/`: scripts that recompute the paper's tables and figures, and the C program for the
  empirical densities.
- `paper/`: the paper (`paper.tex`, `paper.pdf`), its TikZ figures (`figures/*.tex`), raster
  figures (`figures/*.png`) and generated tables (`tables/*.tex`).

## Building

```
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean scripts/Axioms.lean
```

Toolchain: `leanprover/lean4:v4.34.1`, Mathlib `v4.34.1`.

## Reproducing the paper

From the repository root:

```
python3 code/tables.py                      # tables, rechecked from the Lean sources
cc -O2 -o /tmp/rho_density code/rho_density.c -lm
/tmp/rho_density 100000000 > code/data/rho_density.csv   # about 10 s
python3 code/figures.py                     # needs matplotlib
cd paper && latexmk -pdf paper.tex
```

`python3 verification/open_case/final_boxes.py` (needs sympy) reruns the box search and
`python3 verification/open_case/gen_closure.py` regenerates `ErdosSar/Closure.lean`; both
reproduce the committed files.

## Authors

Deep Bhattacharjee, Priyabrata Mandal (corresponding author, priyabrata@manit.ac.in) and
Shounak Bhattacharya.

## License

CC BY 4.0, see `LICENSE`. Archive metadata for Zenodo is in `.zenodo.json`.
