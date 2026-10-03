import numpy as np
N=2*10**7
rho=np.ones(N+1)
isp=np.ones(N+1,bool); isp[:2]=False
for p in range(2,int(N**0.5)+1):
    if isp[p]: isp[p*p::p]=False
for p in np.nonzero(isp)[0]:
    if p>=5: rho[p::p]*=(1-1/p)
idx=np.arange(N+1)
T=rho[(idx%6==3)]; U=rho[(idx%6==1)|(idx%6==5)]
xs=np.round(np.arange(0.50,1.0001,0.01),2)
GT=[(T<x).mean() for x in xs]; GU=[(U<x).mean() for x in xs]
np.save('GT.npy',np.array(GT)); np.save('GU.npy',np.array(GU)); np.save('xs.npy',xs)
for x,a,b in zip(xs,GT,GU):
    if abs(x*20-round(x*20))<1e-9: print(x,round(a,5),round(b,5))
