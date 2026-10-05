"""Recompute, in exact rational arithmetic, every number shown in the tables of the paper.

The constants are read from the Lean sources (ErdosSar/Cert.lean, ErdosSar/Certs.lean) and from
verification/open_case/boxes.json, so the tables cannot drift from the formal proof.  The script
rechecks each certificate inequality certSum(theta') + 7/10^6 <= beta and each box inequality,
and writes the LaTeX tables to paper/tables/.

Run from the repository root:  python3 code/tables.py
"""
import json
import os
import re
from fractions import Fraction as Fr

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'paper', 'tables')
P19 = [5, 7, 11, 13, 17, 19]
MENU = [0, 3, 6, 10, 15, 20, 25, 30, 40, 50, 60, 70, 85, 99]
EPS = Fr(5, 10**4)


def src(path):
    return open(os.path.join(ROOT, path), encoding='utf-8').read()


def frac(s):
    s = s.replace(' ', '')
    return Fr(s) if '/' in s else Fr(int(s))


# F-hat from Cert.lean
FH = {0: Fr(1)}
for m, v in re.findall(r'\|\s*(\d+)\s*=>\s*([0-9]+\s*/\s*[0-9]+)', src('ErdosSar/Cert.lean')):
    FH[int(m)] = frac(v)
assert sorted(FH) == MENU, sorted(FH)

# the sixteen certificates from Certs.lean
certs = []
for th, be, thp in re.findall(
        r'BadBound \(\((\d+ / \d+) : ℚ\) : ℝ\) \(\((\d+ / \d+) : ℚ\) : ℝ\) :=\s*'
        r'badBound_of_cert \(θ\' := (\d+ / \d+)\)', src('ErdosSar/Certs.lean')):
    certs.append((frac(th), frac(thp), frac(be)))
assert len(certs) == 16


def primes(lo, hi):
    return [p for p in range(lo, hi) if p > 1 and all(p % q for q in range(2, int(p**0.5) + 1))]


def Fq(s, m):
    t = Fr(1)
    for p in primes(s, 200):
        t *= 1 + (Fr(p, p - 1)**m - 1) / p
    return t


def signatures():
    for mask in range(1 << len(P19)):
        S = [p for i, p in enumerate(P19) if mask >> i & 1]
        dens, rS = Fr(1), Fr(1)
        for p in P19:
            if p in S:
                dens /= p
                rS *= Fr(p - 1, p)
            else:
                dens *= Fr(p - 1, p)
        yield dens, rS


def cert_sum(thp):
    return sum(d * min((thp / r)**m * FH[m] for m in MENU) for d, r in signatures())


def dec(x, k=4, up=True):
    """Decimal string of the rational x rounded up (or to nearest) at k digits."""
    D = 10**k
    v = -((-x.numerator * D) // x.denominator) if up else round(x * D)
    return ('%.' + str(k) + 'f') % (v / D)


def tex_frac(x):
    x = Fr(x)
    if x.denominator == 1:
        return str(x.numerator)
    return '%d/%d' % (x.numerator, x.denominator)


os.makedirs(OUT, exist_ok=True)

# Table: F-hat
rows = []
for m in MENU[1:]:
    exact = Fq(23, m) / (1 - Fr(2 * m, 199))
    assert Fq(23, m) <= FH[m] * (1 - Fr(2 * m, 199)), m
    rows.append(r'%d & %s & %s \\' % (m, dec(exact, 8, False), dec(FH[m], 6)))
open(os.path.join(OUT, 'fhat.tex'), 'w').write('\n'.join(rows) + '\n')

# Table: certificates
rows = []
for th, thp, be in certs:
    assert th <= thp * (1 - Fr(1, 10**4))
    cs = cert_sum(thp)
    assert cs + Fr(7, 10**6) <= be, th
    rows.append(r'%s & %s & %s & %s \\' % (dec(th, 3, False), dec(thp, 4, False),
                                          dec(cs + Fr(7, 10**6), 6), dec(be, 4, False)))
    print('theta %.3f  certSum+7e-6 = %.6f  beta = %.4f' % (th, cs + Fr(7, 10**6), be))
open(os.path.join(OUT, 'certificates.tex'), 'w').write('\n'.join(rows) + '\n')

# Tables: boxes
B = json.load(open(os.path.join(ROOT, 'verification', 'open_case', 'boxes.json')))
beta = {Fr(k): Fr(v) for k, v in B['beta'].items()}
assert beta == {th: be for th, _, be in certs}
grid = sorted(beta)


def gridup(x):
    return min(g for g in grid if g >= x)


rows = []
for b in B['T']:
    l0, l1, thT, r1, t2 = (Fr(b[k]) for k in ('l0', 'l1', 'thT', 'r1', 't2'))
    assert Fr(1, 2) + 3 * l1 / 4 + EPS <= thT
    assert Fr(1, 6) + beta[gridup(thT)] / 3 + EPS <= l0
    assert beta[r1] / 3 + EPS <= l0
    assert beta[t2] / 3 + (1 - r1) / 3 + EPS <= l0
    assert thT <= r1 * t2
    rows.append(r'$[%s, %s]$ & %s & %s & %s \\' % (tex_frac(l0), tex_frac(l1), dec(thT, 4, False),
                                                  dec(r1, 3, False), dec(t2, 3, False)))
open(os.path.join(OUT, 'boxes_t.tex'), 'w').write('\n'.join(rows) + '\n')

rows = []
for b in B['GP']:
    d0, d1, a0, a1, s, t1, kap, th = (Fr(b[k]) for k in ('d0', 'd1', 'a0', 'a1', 's', 't1', 'kap', 'th'))
    gp = b['mode'] == 'GP'
    thw = Fr(b['thw']) if gp else s
    sw = min(thw, s)
    assert Fr(1, 2) + d1 / 2 + 3 * kap + EPS <= th
    assert beta[s] / 2 + EPS <= d0 / 3 + a0
    assert beta[t1] / 2 + EPS <= Fr(1, 6) + d0 / 3 + a0
    assert th <= t1 * s and d1 + EPS <= t1 * sw
    assert beta[gridup(th)] / 2 + EPS <= d0 / 3 + a0
    if gp:
        assert kap < d1 / 6 + EPS and sw <= thw
        assert beta[thw] / 3 + EPS <= d0 / 6 + a0 + kap
        assert d1 / 6 - kap + a1 + EPS <= thw * sw / 6
    else:
        assert not kap < d1 / 6 + EPS
    rows.append(r'$[%s, %s]$ & $[%s, %s]$ & %s & %s & %s & %s & %s & %s \\' % (
        tex_frac(d0), tex_frac(d1), tex_frac(a0), tex_frac(a1), 'II' if gp else 'I',
        dec(s, 3, False), dec(t1, 3, False), dec(kap, 4, False) if kap else '0', dec(th, 4, False),
        dec(thw, 3, False) if gp else '--'))
open(os.path.join(OUT, 'boxes_gp.tex'), 'w').write('\n'.join(rows) + '\n')
print('tables written to', OUT)
