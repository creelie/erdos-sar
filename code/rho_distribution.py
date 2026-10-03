import numpy as np
N=10**7
# smallest prime factor sieve to compute rho'(z)=prod_{p|z,p>=5}(1-1/p) for odd z
rho=np.ones(N+1)
is_p=np.ones(N+1,bool); is_p[:2]=False
for p in range(2,int(N**0.5)+1):
    if is_p[p]: is_p[p*p::p]=False
for p in np.nonzero(is_p)[0]:
    if p>=5: rho[p::p]*=(1-1/p)
odd=rho[1::2]
for x in [0.4,0.45,0.5,0.55,0.6,0.65,0.7,0.75,0.8,0.85,0.9]:
    print(x, (odd<x).mean())
# also among odd multiples of 3 (T3) vs coprime to 3
t3=rho[3::6]; print("T3 frac rho'<0.55:",(t3<0.55).mean(),"<0.75",(t3<0.75).mean())
