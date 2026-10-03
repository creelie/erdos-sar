"""Rigorous re-check of the constants in Lemma 2.4 (moment bound) of the paper.

Uses mpmath interval arithmetic (outward rounding) for the finite product over
primes p < P0, and the paper's explicit tail bound
    sum_{p >= P0} log(1 + g(p)/p) <= 2m/(P0 - 1)
for the remaining primes. Prints certified upper bounds for
    0.56^40 * Pi_{5,40}   and   0.75^60 * Pi_{11,60}.
Requires: mpmath, sympy.   Run: python3 constants_interval.py [P0]
"""
import sys
from mpmath import iv
from sympy import primerange

iv.dps = 30
P0 = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6


def bound(x, s, m):
    logsum = iv.mpf(0)
    for p in primerange(max(s, 5), P0):
        P = iv.mpf(p)
        g = (1 - 1 / P) ** (-m) - 1
        logsum += iv.log(1 + g / P)
    tail = iv.mpf(2 * m) / (P0 - 1)
    total = iv.mpf(x) ** m * iv.exp(logsum + tail)
    # the decimal literal x is itself enclosed in an interval by iv.mpf
    return total.b  # certified upper endpoint


if __name__ == "__main__":
    b1 = bound("0.56", 5, 40)
    b2 = bound("0.75", 11, 60)
    print(f"P0 = {P0}")
    print(f"0.56^40 * Pi_(5,40)  <= {iv.nstr(iv.mpf(b1), 8)}   (paper: <= 5.82e-4)")
    print(f"0.75^60 * Pi_(11,60) <= {iv.nstr(b2, 8)}   (paper: <= 3.09e-4)")
    assert b1 <= 5.82e-4 and b2 <= 3.09e-4
    print("OK: both constants certified.")
