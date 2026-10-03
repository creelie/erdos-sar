import numpy as np, rigdens
xs=np.round(np.arange(0.50,1.0001,0.01),2)
G=[]
for x in xs:
    G.append(min(1.0,rigdens.G_upper(x)) if x<0.995 else 1.0)
    print(x,G[-1],flush=True)
np.save('GR.npy',np.array(G))
