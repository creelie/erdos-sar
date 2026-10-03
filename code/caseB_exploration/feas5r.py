import numpy as np, itertools, sys
xs=np.load('/root/work/xs.npy'); GT=np.load('/root/work/GR.npy'); GU=GT
RG=np.round(np.arange(0.56,0.97,0.01),2)
def Gv(arr,r):
    i=np.ceil(np.round((r-0.5)/0.01,9)).astype(int); i=np.clip(i,0,len(xs)-1); return arr[i]
eta=0.01; RM=0.75; RS=0.95*RM
def minr(dfun,need):
    # smallest r in RG with dfun(r)>=need (vectorized over leading dims); returns 9 if none
    out=np.full(np.shape(need),9.0)
    for r in RG[::-1]:
        out=np.where(dfun(r)>=need, r, out)
    return out
def check(eps,sig,tau,alpha,lam,step=0.025):
    for RM in (0.9,0.85,0.8,0.75,0.7):
        if check1(eps,sig,tau,alpha,lam,step,RM): return True
    return False
def check1(eps,sig,tau,alpha,lam,step,RM):
    RS=0.95*RM
    aS,aT,aE,aU=0.5-sig,0.5-tau,1-eps,alpha
    g=np.arange(0,lam+1e-9,step)
    m1T,m1U=np.meshgrid(g,g,indexing='ij'); m1T=m1T.ravel(); m1U=m1U.ravel()
    keep=m1T+m1U<=lam+1e-9; m1T=m1T[keep]; m1U=m1U[keep]
    m2=lam-m1T-m1U
    fr=np.array([0,0.25,0.5,0.75,1.0])
    fE,fU,fT=[a.ravel() for a in np.meshgrid(fr,fr,fr,indexing='ij')]
    M=len(m1T); F=len(fE)
    m1T=np.repeat(m1T,F); m1U=np.repeat(m1U,F); m2=np.repeat(m2,F)
    fE=np.tile(fE,M); fU=np.tile(fU,M); fT=np.tile(fT,M)
    use1=(m1T+m1U)>1e-9; use2=m2>1e-9
    remU=aU-m1U-m2
    yE1=np.where(use2, aE*fE, aE); yE2=np.where(use1,aE-yE1,aE); yE1=np.where(use1,yE1,0)
    yU1=np.where(use2, np.maximum(remU,0)*fU, np.maximum(remU,0)); yU2=np.where(use1,np.maximum(remU,0)-yU1,np.maximum(remU,0)); yU1=np.where(use1,yU1,0)
    yT2=np.where(use2,np.maximum(aT-m1T,0),0); yS2=np.where(use2,aS,0)
    m1=m1T+m1U
    Y1=yE1+yU1; need1=np.maximum((0.5+eta)*Y1, m1+2*eta)
    d1=lambda r: Y1-np.minimum(yE1,1-r)-np.minimum(yU1,1-r)
    Y2=yS2+yT2+yE2+yU2; need2=np.maximum((0.5+eta)*Y2, m2+3*eta)
    d2=lambda r: Y2-np.minimum(yS2,0.5*(1-r))-np.minimum(yT2,0.5*(1-r))-np.minimum(yE2,1-r)-np.minimum(yU2,1-r)
    rT1=minr(d1,need1); rU1=rT1; rU2=minr(d2,need2)
    ok=remU>=-1e-9
    ok&=(~use1)|((d1(RS)>=need1)&(rT1<9))
    ok&=(~use2)|((d2(RS)>=need2)&(rU2<9))
    ok&=(m1T<=1e-9)|(m1T<=aT-Gv(GT,np.minimum(rT1,1))/2)
    rr1=np.where(m1U>1e-9,rU1,0.5); rr2=np.where(m2>1e-9,rU2,0.5)
    ok&=(m1U<=aU-Gv(GU,np.minimum(rr1,1))+1e-9)&(m2<=aU-Gv(GU,np.minimum(rr2,1))+1e-9)
    ok&=(m1U+m2<=aU-Gv(GU,np.minimum(np.minimum(rr1,rr2),1))+1e-9)
    # matched pairs: U-type needed when System II used; T or U type if only I
    okU=(aU-Gv(GU,np.array(RM))>=eta)
    okT=(aT-Gv(GT,np.array(RM))/2>=eta)
    ok&=np.where(use2, okU, okU|okT)
    ok&=(m1U+m2+eta<=aU-Gv(GU,np.minimum(np.minimum(np.minimum(rr1,rr2),RM),1))+1e-9)|(~use2 & okT)
    return ok.any()
if __name__=="__main__":
    bad=[]
    E=np.arange(0.045,1.0001,0.05)
    for eps in E:
      for sig in np.arange(0,0.5001,0.1):
        for tau in np.arange(0,0.5001,0.1):
          for alpha in np.arange(0,1.0001,0.05):
            if alpha<eps+sig+tau-1e-9 or alpha>1: continue
            for lam in [0.2,0.4,0.5]:
              if not check(eps,sig,tau,alpha,lam): bad.append((round(eps,3),round(sig,2),round(tau,2),round(alpha,2),lam))
    print(len(bad)); print(bad[:80],flush=True)
