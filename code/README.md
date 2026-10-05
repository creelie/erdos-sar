# Scripts for the paper

Run everything from the repository root.

- `tables.py`: reads the constants `F̂_m` from `ErdosSar/Cert.lean`, the sixteen certificates from
  `ErdosSar/Certs.lean` and the boxes from `verification/open_case/boxes.json`, rechecks in exact
  rational arithmetic every certificate inequality `cert(θ') + 7·10⁻⁶ ≤ β` and every box inequality
  of Lemmas 8.3 and 8.4, and writes Tables 1 to 4 to `paper/tables/`. Standard library only.

  `python3 code/tables.py`

- `rho_density.c`: sieves `ρ'(z) = ∏_{p | z, p ≥ 5}(1 − 1/p)` for `z ≤ N` and prints, for 121
  thresholds `θ` from 0.40 to 1.00, the proportion of odd numbers and of units (`z ≡ ±1 mod 6`)
  with `ρ'(z) < θ`. The output for `N = 10⁸` is `data/rho_density.csv`. These numbers are an
  illustration for Figure 4 and play no part in the proof.

  `cc -O2 -o /tmp/rho_density code/rho_density.c -lm`
  `/tmp/rho_density 100000000 > code/data/rho_density.csv`

- `figures.py`: draws `paper/figures/boxes.png` (Figure 9, the box cover) and
  `paper/figures/densities.png` (Figure 4, certified bounds against the data above). Needs
  matplotlib.

  `python3 code/figures.py`

The TikZ figures are in `paper/figures/*.tex` and are compiled with the paper.
