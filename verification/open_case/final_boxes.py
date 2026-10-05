"""Search for the box cover of the open case.

Computes certified density bounds beta(theta) on a grid of thresholds (signatures over the primes
5..19, the same menu of moment exponents as ErdosSar/Cert.lean), then covers the parameter region by
boxes: intervals of lambda = mu_T/n for the unit construction and boxes of (delta, a) = (3d/n, mu_6/n)
for the giant-path construction.  The result is written to boxes.json next to this script, which
gen_closure.py turns into ErdosSar/Closure.lean.
"""
import json, os, sys
from fractions import Fraction as Fr
from sympy import primerange
QP = 19
P = list(primerange(5, QP+1))
MENU = [0, 3, 6, 10, 15, 20, 25, 30, 40, 50, 60, 70, 85, 99]
def Fq(s, m):
    t = Fr(1)
    for p in primerange(s, 200):
        t *= 1 + (Fr(p, p-1)**m - 1)/p
    return t
def roundup(x, digs=6):
    # rational upper bound with denominator 10^digs
    D = 10**digs
    return Fr(-((-x.numerator*D)//x.denominator), D)
FH = {}
for m in MENU:
    if m == 0: FH[m] = Fr(1); continue
    FH[m] = roundup(Fq(QP+1, m)/(1 - Fr(2*m, 199)))
def beta(theta_p):
    # certified class density of {rho' < theta} using theta' = theta_p (already inflated)
    tot = Fr(0)
    for mask in range(1 << len(P)):
        dens = Fr(1); rS = Fr(1)
        for i, p in enumerate(P):
            if mask >> i & 1: dens /= p; rS *= Fr(p-1, p)
            else: dens *= Fr(p-1, p)
        t = theta_p/rS
        best = min(t**m * FH[m] for m in MENU)
        best = min(best, Fr(1))
        tot += dens*best
    return tot
STEP = Fr(1, 40)
GRID = [Fr(1,2) + STEP*j for j in range(21)]
INFL = Fr(2, 10000)
MARKOV = Fr(1, 10**5)   # Markov share (relative), added to beta
BV = {}
for g in GRID:
    if g >= 1: BV[g] = Fr(1); continue
    BV[g] = beta(g + INFL) + MARKOV
def rup(x, d=4):
    return roundup(x, d)
BVr = {g: min(Fr(1), rup(BV[g])) for g in GRID}   # 4-digit rational upper bounds used in boxes
eps = Fr(5, 10000)
def gridup(x):
    for g in GRID:
        if g >= x: return g
    return None
KAPS = [Fr(j, 400) for j in range(41)]
def gp_params(d0, d1, a0, a1):
    for s in GRID:
        if not (d0/3 + a0 >= BVr[s]/2 + eps): continue
        for t1 in GRID:
            if not (Fr(1,6) + d0/3 + a0 >= BVr[t1]/2 + eps): break
            # Q1 mode
            kap = d1/6 + eps
            th = Fr(1,2) + d1/2 + 3*kap + eps
            if gridup(th) and t1*s >= th and t1*s >= d1 + eps and d0/3 + a0 >= BVr[gridup(th)]/2 + eps:
                return dict(mode='Q1', s=s, t1=t1, kap=kap, th=th, thw=None)
            for kap in KAPS:
                if kap >= d1/6: break
                th = Fr(1,2) + d1/2 + 3*kap + eps
                if gridup(th) is None or t1*s < th: break
                if not (d0/3 + a0 >= BVr[gridup(th)]/2 + eps): continue
                for thw in GRID:
                    mm = min(thw, s)
                    if t1*mm < d1 + eps: continue
                    if d0/6 + a0 + kap < BVr[thw]/3 + eps: continue
                    if thw*mm/6 < d1/6 - kap + a1 + eps: continue
                    return dict(mode='GP', s=s, t1=t1, kap=kap, th=th, thw=thw)
    return None
def t_params(l0, l1):
    thT = Fr(1,2) + Fr(3,4)*l1 + eps
    if gridup(thT) is None or l0 < Fr(1,6) + BVr[gridup(thT)]/3 + eps: return None
    for r1 in GRID:
        if l0 < BVr[r1]/3 + eps: break
        t2 = gridup(thT/r1)
        if t2 is None: continue
        if l0 >= BVr[t2]/3 + (1 - r1)/3 + eps: return dict(thT=thT, r1=r1, t2=t2)
    return None
cT = Fr(9, 50)
tb = []; l0 = cT
while l0 < Fr(1,3):
    for w in [Fr(1,5), Fr(1,10), Fr(1,20), Fr(1,50), Fr(1,100), Fr(1,200)]:
        p = t_params(l0, min(l0 + w, Fr(1,3)))
        if p: break
    else: print('T FAIL', float(l0)); sys.exit(1)
    l1 = min(l0 + w, Fr(1,3)); tb.append(dict(l0=l0, l1=l1, **p)); l0 = l1
gb = []; d0 = Fr(3, 70)
while d0 < 3*cT:
    for dw in [Fr(1,10), Fr(1,20), Fr(1,40), Fr(1,80), Fr(1,160), Fr(1,320), Fr(1,640), Fr(1,1280)]:
        d1 = min(d0 + dw, 3*cT); a0 = Fr(0); strip = []; ok = True
        amax = cT - d0/3
        while a0 < amax:
            for aw in [Fr(1,5), Fr(1,10), Fr(1,20), Fr(1,40), Fr(1,80), Fr(1,160), Fr(1,320)]:
                a1 = min(a0 + aw, amax); p = gp_params(d0, d1, a0, a1)
                if p: break
            else: ok = False; break
            strip.append(dict(d0=d0, d1=d1, a0=a0, a1=a1, **p)); a0 = a1
        if ok: break
    else: print('GP FAIL', float(d0)); sys.exit(1)
    gb += strip; d0 = d1
used = set()
for b in tb: used |= {gridup(b['thT']), b['r1'], b['t2']}
for b in gb: used |= {b['s'], b['t1'], gridup(b['th'])} | ({b['thw']} if b['thw'] else set())
print('T boxes', len(tb), 'GP boxes', len(gb), 'thresholds', sorted(float(x) for x in used))
for b in tb: print({k: (str(v) if isinstance(v, Fr) else v) for k, v in b.items()})
for b in gb: print({k: (str(v) if isinstance(v, Fr) else v) for k, v in b.items()})
print({str(g): str(BVr[g]) for g in sorted(used)})
json.dump(dict(T=[{k: str(v) for k, v in b.items()} for b in tb], GP=[{k: str(v) for k, v in b.items()} for b in gb],
               beta={str(g): str(BVr[g]) for g in sorted(used)}, FH={m: str(FH[m]) for m in MENU}),
          open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'boxes.json'), 'w'), indent=1)
