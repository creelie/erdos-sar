import math
from sympy import primerange
P0=10**7
primes=list(primerange(5,P0))
def logPi(m,pmin):
    s=0.0
    for p in primes:
        if p<pmin: continue
        s+=math.log1p(((1-1/p)**(-m)-1)/p)
    assert m/(P0-1)<=1
    return s+2*m/(P0-1)   # tail: sum_{p>=P0} log(1+g/p) <= sum 2m/(p(p-1)) <= 2m/(P0-1)
# hard threshold
m=40; v=0.56**m*math.exp(logPi(m,5)); print("F(0.56)/n <=",v)
best=min((0.75**m*math.exp(logPi(m,11)),m) for m in range(1,80)); print("G'/n (primes>=11, rho<0.75) <=",best)
best2=min((0.75**m*math.exp(logPi(m,11))*12/35,m) for m in range(1,80)); print("restricted to odd, coprime 35 <=",best2)
