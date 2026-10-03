import itertools, math, sys
def T(n): return n//2+n//3-n//6
def has_cycle_len(adj, verts, L):
    # adj: dict v->bitmask over indices; verts list of indices; find simple cycle of length L
    nv=len(verts)
    # DFS from smallest vertex in cycle
    for s in range(nv):
        # only vertices > s allowed besides s
        allowed=((1<<nv)-1) & ~((1<<(s+1))-1)
        stack=[(s,1<<s,1)]
        while stack:
            v,used,d=stack.pop()
            nb=adj[v]
            if d==L:
                if nb>>s &1: return True
                continue
            cand=nb & allowed & ~used
            while cand:
                b=cand & -cand; u=b.bit_length()-1; cand^=b
                stack.append((u,used|b,d+1))
    return False
def check(n):
    t=T(n); k=t+1
    Ls=[L for L in range(3,int(n/3+1)+1) if L%2==1]
    bad=[]
    cnt=0
    for A in itertools.combinations(range(1,n+1),k):
        cnt+=1
        nv=len(A)
        adj=[0]*nv
        for i in range(nv):
            for j in range(i+1,nv):
                if math.gcd(A[i],A[j])==1:
                    adj[i]|=1<<j; adj[j]|=1<<i
        for L in Ls:
            if not has_cycle_len(adj,A,L):
                bad.append((A,L)); break
        if len(bad)>5: break
    return cnt,bad
for n in range(int(sys.argv[1]),int(sys.argv[2])):
    cnt,bad=check(n)
    print(n,"T=",T(n),"checked",cnt,"bad",bad[:3],flush=True)
