import json, sys
from fractions import Fraction as Fr
import os
HERE = os.path.dirname(os.path.abspath(__file__))
B = json.load(open(os.path.join(HERE, 'boxes.json')))
beta = {Fr(k): Fr(v) for k, v in B['beta'].items()}
names = {"11/20": "bad_550", "3/5": "bad_600", "5/8": "bad_625", "13/20": "bad_650", "27/40": "bad_675", "7/10": "bad_700", "29/40": "bad_725", "3/4": "bad_750", "31/40": "bad_775", "4/5": "bad_800", "33/40": "bad_825", "17/20": "bad_850", "7/8": "bad_875", "9/10": "bad_900", "37/40": "bad_925", "19/20": "bad_950"}
fld = {Fr(k): v.replace('bad_', 'b') for k, v in names.items()}
GRID = sorted(beta)
eps = Fr(5, 10000)
def gridup(x):
    for g in GRID:
        if g >= x: return g
    raise Exception('no grid point above %s' % x)
def q(x):
    x = Fr(x)
    if x.denominator == 1: return '(%d : ℚ)' % x.numerator
    return '(%d / %d : ℚ)' % (x.numerator, x.denominator)
def chk(c, msg):
    if not c: print('FAIL', msg); sys.exit(1)
out = []
# ---- T boxes
tb = [{k: (Fr(v) if v != 'None' else None) for k, v in b.items()} for b in B['T']]
def tcall(b):
    l0, l1, thT, r1, t2 = b['l0'], b['l1'], b['thT'], b['r1'], b['t2']
    gT = gridup(thT)
    chk(Fr(1,2) + 3*l1/4 + eps <= thT, 'C1')
    chk(Fr(1,6) + beta[gT]/3 + eps <= l0, 'C2')
    chk(beta[r1]/3 + eps <= l0, 'C3')
    chk(beta[t2]/3 + (1 - r1)/3 + eps <= l0, 'C4')
    chk(thT <= r1*t2, 'C5')
    args = [l0, l1, thT, r1, t2, gT, r1, t2, beta[gT], beta[r1], beta[t2]]
    at = ['exact', 't_box', 'hn', 'hA', 'hcard', 'hl2', 'hl'] + [q(a) for a in args]
    at += ['(by push_cast; linarith)'] * 2
    at += ['hb.%s' % fld[gT], 'hb.%s' % fld[r1], 'hb.%s' % fld[t2]]
    at += ['(by norm_num)'] * 9
    return at
# ---- GP boxes
gb = [{k: (Fr(v) if v not in ('None', 'GP', 'Q1') else v) for k, v in b.items()} for b in B['GP']]
def gpcall(b):
    d0, d1, a0, a1, s, t1, kap, th = b['d0'], b['d1'], b['a0'], b['a1'], b['s'], b['t1'], b['kap'], b['th']
    if b['mode'] == 'GP':
        thw = b['thw']; sw = min(thw, s)
    else:
        thw = s; sw = s
    gs, gt1, gth, gthw = s, t1, gridup(th), thw
    chk(gs in beta and gt1 in beta and gthw in beta, 'grid')
    chk(0 <= t1 and 0 <= thw and 0 <= kap and sw <= s and d1 <= Fr(9,10), 'basic')
    chk(Fr(1,2) + d1/2 + 3*kap + eps <= th, 'B1')
    chk(beta[gs]/2 + eps <= d0/3 + a0, 'BP')
    chk(beta[gt1]/2 + eps <= Fr(1,6) + d0/3 + a0, 'BG')
    chk(th <= t1*s, 'BH')
    chk(d1 + eps <= t1*sw, 'BE')
    chk(beta[gth]/2 + eps <= d0/3 + a0, 'BS')
    if b['mode'] == 'GP':
        chk(kap < d1/6 + eps, 'mode')
        chk(beta[gthw]/3 + eps <= d0/6 + a0 + kap, 'W')
        chk(d1/6 - kap + a1 + eps <= thw*sw/6, 'Y')
        chk(sw <= thw, 'swthw')
        bwy = '(fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)'
    else:
        chk(not (kap < d1/6 + eps), 'Q1mode')
        bwy = '(fun h => by norm_num at h)'
    args = [d0, d1, a0, a1, s, t1, th, thw, sw, kap, gs, gt1, gth, gthw, beta[gs], beta[gt1], beta[gth], beta[gthw]]
    at = ['exact', 'gp_box', 'hn', 'hA', 'hcard', 'hl2', 'hl'] + [q(a) for a in args]
    at += ['(by push_cast; linarith)'] * 4
    at += ['hb.%s' % fld[x] for x in (gs, gt1, gth, gthw)]
    at += ['(by norm_num)'] * 15 + [bwy]
    return at
# check coverage structure
strips = []
for b in gb:
    if strips and strips[-1][0] == (b['d0'], b['d1']): strips[-1][1].append(b)
    else: strips.append(((b['d0'], b['d1']), [b]))
chk(strips[0][0][0] == Fr(3,70), 'first strip')
for i in range(1, len(strips)): chk(strips[i][0][0] == strips[i-1][0][1], 'strip chain')
chk(strips[-1][0][1] == Fr(27,50), 'last strip')
for (d0, d1), bs in strips:
    chk(bs[0]['a0'] == 0, 'a0')
    for i in range(1, len(bs)): chk(bs[i]['a0'] == bs[i-1]['a1'], 'a chain')
    chk(bs[-1]['a1'] == Fr(9,50) - d0/3, 'a last')
chk(tb[0]['l0'] == Fr(9,50) and tb[-1]['l1'] == Fr(1,3), 'T range')
for i in range(1, len(tb)): chk(tb[i]['l0'] == tb[i-1]['l1'], 'T chain')

def ind(k): return '  ' * k
def wrap(s, k):
    # wrap a long tactic line into continuation lines indented by 4 more spaces
    words = s if isinstance(s, list) else [s]
    lines = []; cur = ind(k)
    first = True
    for w in words:
        lim = 100
        if len(cur) + len(w) + 1 > lim and cur.strip():
            lines.append(cur.rstrip())
            cur = ind(k) + '    '
        cur += w + ' '
    lines.append(cur.rstrip())
    return lines
def rq(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d / %d' % (x.numerator, x.denominator)
def bullet(lines, k):
    # lines start at indent k+1; turn into a bullet at indent k
    out = list(lines)
    out[0] = ind(k) + '· ' + out[0].lstrip()
    return out
def chain(items, k, split, leaf):
    if len(items) == 1: return leaf(items[0], k)
    lines = wrap(split(items[0]), k)
    lines += bullet(leaf(items[0], k + 1), k)
    lines += bullet(chain(items[1:], k + 1, split, leaf), k)
    return lines
T_lines = chain(tb, 1, lambda b: 'rcases le_or_gt (μT : ℝ) (%s * n + 1) with h | h' % rq(b['l1']),
                lambda b, k: wrap(tcall(b), k))
def strip_leaf(st, k):
    (d0, d1), bs = st
    return chain(bs, k, lambda b: 'rcases le_or_gt (μ6 : ℝ) (%s * n) with ha | ha' % rq(b['a1']),
                 lambda b, kk: wrap(gpcall(b), kk))
CTX = r"""{n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) {l : ℕ} (hl2 : 2 ≤ l) (hl : 6 * l ≤ n)"""
PRE = r"""  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
  have hμ60 : (0 : ℝ) ≤ μ6 := Nat.cast_nonneg _
"""
lemmas = []
lemmas.append(r"""/-- The unit construction covers `μ_T ≥ 9n/50`. -/
theorem open_T """ + CTX + r"""
    (hT : 9 * (n : ℝ) ≤ 50 * (Pool23 n \ A).card) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
""" + PRE + r"""  have hμTn : (μT : ℝ) ≤ n / 3 := by
    have hTn : T n = n / 2 + n / 3 - n / 6 := rfl
    have : 3 * μT ≤ n := by omega
    have : (3 : ℝ) * μT ≤ n := by exact_mod_cast this
    linarith
""" + '\n'.join(T_lines))
for idx, st in enumerate(strips):
    (d0, d1) = st[0]
    lines = strip_leaf(st, 1)
    h1name = '_hδ1' if idx == len(strips) - 1 else 'hδ1'
    lemmas.append(r"""set_option maxHeartbeats 1000000 in
/-- The giant-path construction for `%s ≤ 3d/n ≤ %s`. -/
theorem open_GP_%d """ % (rq(d0), rq(d1), idx) + CTX + r"""
    (hT : 50 * ((Pool23 n \ A).card : ℝ) < 9 * n)
    (hδ0 : (%s : ℝ) * n ≤ 3 * (Estar n \ A).card) (%s : 3 * ((Estar n \ A).card : ℝ) ≤ %s * n) :
    HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
""" % (rq(d0), h1name, rq(d1)) + PRE + '\n'.join(lines))
def gp_split(st):
    return 'rcases le_or_gt (3 * (d : ℝ)) (%s * n) with hδ | hδ' % rq(st[0][1])
def gp_leaf(st, k):
    idx = strips.index(st)
    return wrap(['exact', 'open_GP_%d' % idx, 'hn', 'hb', 'hA', 'hcard', 'hl2', 'hl', 'hT', '(by linarith)', '(by linarith)'], k)
G_lines = chain(strips, 2, gp_split, gp_leaf)
body = ['  rcases le_or_gt (9 * (n : ℝ)) (50 * μT) with hT | hT']
body += ['  · exact open_T hn hb hA hcard hl2 hl hT']
body += bullet(G_lines, 1)
fields = '\n'.join('  %s : BadAt n ((%s : ℚ) : ℝ) ((%s : ℚ) : ℝ)' % (fld[g], rq(g), rq(beta[g])) for g in GRID)
nm = [names[str(g)] for g in GRID]
obt = '\n'.join('  obtain ⟨N%d, h%d⟩ := badAt_of_badBound %s' % (i, i, n_) for i, n_ in enumerate(nm))
summ = ' + '.join('N%d' % i for i in range(len(nm)))
mk = ', '.join('h%d n (by omega)' % i for i in range(len(nm)))
header = r"""import ErdosSar.Boxes
import ErdosSar.Certs
import ErdosSar.Main

/-!
# Erdős Problem #883, Question 1

The case `70 |E* \ A| ≤ n` is paper Theorem 1.1 (`question1_restricted`). In the remaining case
the proportion `μ_T/n` of multiples of `2` or `3` missing from `A` decides the construction: the
unit construction (`t_box`) when `μ_T ≥ 9n/50`, and the giant-path construction (`gp_box`)
otherwise, on a finite cover of the possible values of `(3d/n, μ₆/n)` by boxes. Each box uses the
density certificates of `Certs.lean` at its thresholds. The case split below is generated from
`verification/open_case/boxes.json` by `verification/open_case/gen_closure.py`.
-/

namespace ErdosSar

open Finset

/-- The certified bounds at the sixteen thresholds, for one `n`. -/
structure Bads (n : ℕ) : Prop where
""" + fields + r"""

theorem bads_eventually : ∃ N, ∀ n ≥ N, Bads n := by
""" + obt + r"""
""" + '\n'.join(wrap(['refine', '⟨' + summ.split(' + ')[0]] + ['+ ' + x for x in summ.split(' + ')[1:-1]] + ['+ ' + summ.split(' + ')[-1] + ',', 'fun', 'n', 'hn', '=>', '?_⟩'], 1)) + '\n' + '\n'.join(wrap(['exact', '⟨' + mk.split(', ')[0] + ','] + [x + ',' for x in mk.split(', ')[1:-1]] + [mk.split(', ')[-1] + '⟩'], 1)) + r"""

""" + '\n\n'.join(lemmas) + r"""

/-- **The open case.** If `A` omits more than `n/70` elements of `E*(n)`, the coprime graph of `A`
still contains every cycle of length `2l + 1` with `2 ≤ l ≤ n/6`. -/
theorem open_case {n : ℕ} (hn : N₁ ≤ n) (hb : Bads n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : T n < A.card) (hD : n < 70 * (Estar n \ A).card) {l : ℕ} (hl2 : 2 ≤ l)
    (hl : 6 * l ≤ n) : HasCycleOfLength (coprimeGraph A) (2 * l + 1) := by
  obtain ⟨-, hu, hdμ, hUn, -⟩ := open_counts hA hcard
  set d := (Estar n \ A).card with hd
  set μ6 := (M6 n \ A).card with hμ6
  set μT := (Pool23 n \ A).card with hμT
  have hdR : (n : ℝ) < 70 * d := by exact_mod_cast hD
  have hdμR : (d : ℝ) + μ6 ≤ μT := by exact_mod_cast hdμ
"""
footer = r"""

/-- **Erdős Problem #883, Question 1**, formally verified: for all large `n`, every `A ⊆ [1, n]`
with `|A| > T(n)` has a coprime graph containing every odd cycle of length at most `n/3 + 1`. -/
theorem question1 : Question1 := by
  obtain ⟨n₀, h₀⟩ := question1_restricted
  obtain ⟨Nb, hNb⟩ := bads_eventually
  refine ⟨n₀ + N₁ + Nb, fun n hn A hA hcard L hL h3 hLn => ?_⟩
  have hn13 : 13 ≤ n := le_trans (by unfold N₁; norm_num) (show N₁ ≤ n by omega)
  by_cases hD : 70 * (Estar n \ A).card ≤ n
  · exact h₀ n (by omega) A hA hcard hD L hL h3 hLn
  · obtain ⟨l, rfl⟩ := hL
    rcases (by omega : l = 1 ∨ 2 ≤ l) with rfl | hl2
    · exact triangle hn13 A hA hcard
    · exact open_case (by omega) (hNb n (by omega)) hA hcard (by omega) hl2 (by omega)

end ErdosSar
"""
open(os.path.join(HERE, '..', '..', 'ErdosSar', 'Closure.lean'), 'w').write(header + '\n'.join(body) + footer)
print('boxes T', len(tb), 'GP', len(gb), 'strips', len(strips))
