# Code accompanying "Odd cycles of every length up to 2o(n)+1 in coprime graphs of sets containing almost all even numbers"

Requirements: Python 3, numpy, sympy.

- `constants.py` — computes the moment-bound constants of Lemma 2.4:
  0.56^40 * Pi_{5,40} <= 5.82e-4 and 0.75^60 * Pi_{11,60} <= 3.09e-4.
  Product over primes < 10^7 in double precision, plus the explicit tail bound 2m/(P0-1).
  Run: `python3 constants.py`
- `bruteforce_small_n.py` — exhaustive check of Question 1 for small n: every A ⊆ [n]
  with |A| = T(n)+1 has all odd cycles of length <= n/3+1 in its coprime graph.
  Run: `python3 bruteforce_small_n.py 6 22` (checks n = 6..21; no counterexample).
- `rho_distribution.py` — empirical distribution of rho'(z) = prod_{p|z, p>=5}(1-1/p) over odd z <= 10^7
  (sanity check only; not used in the proof).
