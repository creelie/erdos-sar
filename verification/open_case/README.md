# Box data for the case 70d > n

- `boxes.json`: the sixteen certificate thresholds `θ` with their bounds `β(θ)`, the three
  intervals of `λ = μ_T/n` for the unit construction (Lemma 8.3 of the paper) and the 29 boxes of
  `(δ, a) = (3d/n, μ₆/n)` for the giant-path construction (Lemma 8.4), with all parameters as
  exact rationals.
- `final_boxes.py`: the search that produced `boxes.json`. It computes certified bounds `β(θ)` by
  the method of Theorem 4.4 and covers the region `3/70 ≤ δ ≤ 27/50`, `0 ≤ a ≤ 9/50 − δ/3` and
  the interval `9/50 ≤ λ ≤ 1/3`. Needs sympy.
- `gen_closure.py`: turns `boxes.json` into `ErdosSar/Closure.lean`, which applies `t_box` and
  `gp_box` to each interval and box and proves `question1`. Edit the generator, not the generated
  file.

Both scripts reproduce the committed files exactly:

```
python3 verification/open_case/final_boxes.py
python3 verification/open_case/gen_closure.py
git diff --stat
```
