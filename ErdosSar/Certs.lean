import ErdosSar.Cert

/-!
# The density certificates

Each theorem `bad_θ` states `BadBound θ β`: for all large `n` and every symmetric set `R` of
residues mod 6, at most `(n/6) |R| β` integers `z ≤ n` with `z mod 6 ∈ R` have `ρ'(z) < θ`.
The rational inequality behind each one is checked by the kernel.
-/

namespace ErdosSar

set_option maxRecDepth 100000 in
theorem bad_550 : BadBound ((11 / 20 : ℚ) : ℝ) ((3 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 2751 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_600 : BadBound ((3 / 5 : ℚ) : ℝ) ((7 / 2000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 3001 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_625 : BadBound ((5 / 8 : ℚ) : ℝ) ((1 / 125 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 1563 / 2500) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_650 : BadBound ((13 / 20 : ℚ) : ℝ) ((89 / 5000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 3251 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_675 : BadBound ((27 / 40 : ℚ) : ℝ) ((353 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 422 / 625) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_700 : BadBound ((7 / 10 : ℚ) : ℝ) ((251 / 5000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 3501 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_725 : BadBound ((29 / 40 : ℚ) : ℝ) ((93 / 1250 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 1813 / 2500) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_750 : BadBound ((3 / 4 : ℚ) : ℝ) ((143 / 1250 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 3751 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_775 : BadBound ((31 / 40 : ℚ) : ℝ) ((1049 / 5000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 969 / 1250) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_800 : BadBound ((4 / 5 : ℚ) : ℝ) ((2483 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 4001 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_825 : BadBound ((33 / 40 : ℚ) : ℝ) ((1517 / 5000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 2063 / 2500) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_850 : BadBound ((17 / 20 : ℚ) : ℝ) ((3457 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 4251 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_875 : BadBound ((7 / 8 : ℚ) : ℝ) ((3939 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 547 / 625) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_900 : BadBound ((9 / 10 : ℚ) : ℝ) ((4637 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 4501 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_925 : BadBound ((37 / 40 : ℚ) : ℝ) ((5387 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 2313 / 2500) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

set_option maxRecDepth 100000 in
theorem bad_950 : BadBound ((19 / 20 : ℚ) : ℝ) ((7107 / 10000 : ℚ) : ℝ) :=
  badBound_of_cert (θ' := 4751 / 5000) (by norm_num) (by norm_num) (by
    unfold certSum; decide +kernel)

end ErdosSar
