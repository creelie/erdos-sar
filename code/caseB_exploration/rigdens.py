"""Rigorous upper bounds for the density of {z : rho'(z) < r} inside a residue class
coprime to every prime >= 5 (classes mod 6), uniformly for z <= n, up to an additive
O(2^{pi(B)} / n) error that vanishes as n -> infinity.

rho'(z) = prod_{p | z, p >= 5} (1 - 1/p).

Split primes at B.  Small part X_s = sum_{p|z, 5<=p<=B} a_p with a_p = -log(1-1/p);
large part X_l = sum_{p | z, p > B} a_p.  rho'(z) < r  <=>  X_s + X_l > L := -log r.
For any split L = L1 + L2:  P(X_s + X_l > L) <= P(X_s > L1) + P(X_l > L2).
P(X_s > L1): exact distribution (independent Bernoulli(1/p) in density), computed by DP
with a_p rounded UP to a grid (so the computed tail is an upper bound).
P(X_l > L2): moment bound  <= exp(-m L2) * prod_{p > B} (1 + (e^{m a_p} - 1)/p).
"""
import math
from sympy import primerange
def small_tail(B, L1, h=1e-4):
    ps=list(primerange(5,B+1))
    M=int(math.ceil(sum(-math.log(1-1/p) for p in ps)/h))+len(ps)+2
    dist=[0.0]*(M+1); dist[0]=1.0
    for p in ps:
        k=int(math.ceil(-math.log(1-1/p)/h))   # rounded up
        q=1.0/p; new=[0.0]*(M+1)
        for i,v in enumerate(dist):
            if v==0: continue
            new[i]+=v*(1-q)
            if i+k<=M: new[i+k]+=v*q
        dist=new
    thr=L1/h
    return sum(v for i,v in enumerate(dist) if i>thr)   # P(rounded X_s > L1) >= P(X_s > L1)
_pl=None
def large_tail(B, L2, m, P0=10**7):
    global _pl
    if _pl is None: _pl=list(primerange(2,P0))
    s=0.0
    for p in _pl:
        if p<=B: continue
        a=-math.log(1-1/p)
        s+=math.log1p((math.exp(m*a)-1)/p)
    # tail p>=P0: (e^{m a}-1)/p <= 2 m a / p <= 4m/p^2  (m a <= 1)
    s+=4*m/(P0-1)
    return math.exp(-m*L2+s)
def G_upper(r, B=300, fr=(0.985,0.99,0.995), ms=(50,100,200,400)):
    L=-math.log(r); best=1.0
    for f in fr:
        L1=-math.log(r/f); L2=L-L1
        st=small_tail(B,L1)
        lt=min(large_tail(B,L2,m) for m in ms)
        best=min(best,st+lt)
    return best
if __name__=="__main__":
    for r in [0.56,0.6,0.65,0.7,0.75,0.8,0.85,0.9]:
        print(r, G_upper(r))
