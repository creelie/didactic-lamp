import sys
from functools import lru_cache
sys.setrecursionlimit(100000)

def lvl(n):
    t=0
    while 3**(t+1)<=n: t+=1
    return t

def lemma1(l):
    """zero-sum triples partitioning [-l,l] (l%3==0: plus singleton 0 returned separately)"""
    assert l%3 in (0,1)
    if l%3==1:
        tr=[(-l,0,l)]; k=(l-1)//3; zero=False
    else:
        tr=[]; k=l//3; zero=True
    for i in range(k):
        tr.append((-(3*k-i),1+i,3*k-1-2*i))
        tr.append((-(2*k-i),-(k-i),3*k-2*i))
    return tr, zero

def I(M):
    assert M%2==1
    ps=[]
    for i in range(1,(M+1)//2+1): ps.append((2*i-1,2*M+1-i))
    for i in range(1,(M-1)//2+1): ps.append((2*i,(3*M+1)//2-i))
    return ps
def X(m):
    if m%2==1: return I(m)
    return [(1,m+1)]+[(a+1,b+2) for (a,b) in I(m-1)]
def shiftpair(m):
    """cross pairing s <-> s+m of [1..2m]; for odd m all deltas even"""
    return [(x,x+m) for x in range(1,m+1)]
def Ttrick(N,inner):
    """pairs (2N-1,2N),(1,N),(2,N+1) plus inner pairing of [1..2(N-3)] mapped by phi"""
    m=N-3
    phi=lambda x: x+2 if x<=m else x+4
    return [(2*N-1,2*N),(1,N),(2,N+1)]+[(phi(a),phi(b)) for (a,b) in inner]
def gadget(N):
    r=(N-1)//3; assert N==3*r+1
    if r==0: return [(1,2)]
    if r%2==1: return Ttrick(N,shiftpair(N-3))
    return Ttrick(N,Ttrick(N-3,shiftpair(N-6)))
def delta_partition(N):
    r=(N-1)//3
    if r==0: return [(0,)]
    parts=[(2*N-2,-N,-(N-2))]
    if r%2==1:
        m=N-3
    else:
        m0=N-3; parts.append((2*m0,-(m0+2),-(m0-2))); m=N-6
    L=(m-1)//2; tr,z=lemma1(L); assert z
    parts+=[tuple(2*d for d in t) for t in tr]+[(0,)]
    return parts
@lru_cache(None)
def part(n):
    if n==0: return ()
    if n==1: return ((1,),)
    if n==2: return ((1,2),)
    t=lvl(n); T=3**t
    if n==T: return part(n-1)+((T,),)
    if n>=(3*T+1)//2:  # upper half of level t
        Q=3*T; n2=Q-1-n
        return part(n2)+tuple((x,Q-x) for x in range(n2+1,(Q-1)//2+1))
    j=n-T
    if j%3==0:
        k=j//3; tr,_=lemma1(3*k)
        return part(T-3*k-1)+((T,),)+tuple(tuple(T+d for d in tt) for tt in tr)
    if j%3==1:
        k=(j-1)//3; tr,_=lemma1(3*k)
        return part(T-3*k-2)+((T-3*k-1,T,T+3*k+1),)+tuple(tuple(T+d for d in tt) for tt in tr)
    # j%3==2 : my construction
    return my(n,T,j)

def find_triple(p,a,b):
    for q in p:
        if a in q and b in q and len(q)==3: return q
    return None

def assemble(n,T,j,offtriples,zero_single,Fparts):
    parts=[]
    used=set()
    D=set()
    for tt in offtriples:
        assert sum(tt)==0
        parts.append(tuple(T+d for d in tt))
        for d in tt:
            if d<0: D.add(-d)
    if zero_single: parts.append((T,))
    Fset=set(x for q in Fparts for x in q)
    Freed=set(d for d in D if T-d not in D)
    assert Fset==Freed, (n,sorted(Fset^Freed)[:10])
    parts+=list(Fparts)
    top=set(T-d for d in D)
    for x in range(1,(T-1)//2+1):
        y=T-x
        if x in top or y in top: continue
        parts.append((x,y))
    return tuple(parts)

def my(n,T,j):
    t=lvl(T)
    if j==2:
        return assemble(n,T,j,[(1,2,-3)],True,[(3,)])
    if j> 3**(t-1):  # case B
        pj=part(j); tr=find_triple(pj,j-1,j)
        assert tr is not None and T-2*j+1 in tr, ('B',n)
        offt=[(j-1,j,-(2*j-1))]
        tr1,z=lemma1(j-2); offt+=tr1
        F=[q for q in pj if q!=tr]
        return assemble(n,T,j,offt,True,F)
    # case A
    u=lvl(j); U=3**u
    if j-U<=(U-1)//2:   # A1: j lower half of its level
        pj=part(j); tr=find_triple(pj,j-1,j)
        assert tr is not None, ('A1',n,j)
        w=[x for x in tr if x not in (j-1,j)][0]
        offt=[(j-1,j,-(2*j-1))]
        tr1,z=lemma1(j-2); offt+=tr1
        F=[q for q in pj if q!=tr]+[(w,2*j-1)]
        return assemble(n,T,j,offt,True,F)
    # A2: gadget, j in upper half of level u, P=3^{u+1}
    P=3*U; c=(P-1)//2; jp=P-1-j; N=j-c
    assert jp%3==0 and N%3==1
    pairs=gadget(N)
    offt=[]
    tr1,z=lemma1(jp); offt+=tr1
    for (x,y) in pairs:
        d1,d2=jp+x,jp+y
        offt.append((d1,d2,-(d1+d2)))
    F=list(part(jp))
    for q in delta_partition(N):
        F.append(tuple(P+d for d in q))
    return assemble(n,T,j,offt,True,F)

def check(n,p):
    allx=sorted(x for q in p for x in q)
    if allx!=list(range(1,n+1)): return 'not partition'
    for q in p:
        s=sum(q)
        if len(q)>3: return ('big',q)
        while s%3==0: s//=3
        if s!=1: return ('sum',q)
    return None

if __name__=='__main__':
    NMAX=int(sys.argv[1])
    bad=[]
    for n in range(1,NMAX+1):
        try:
            p=part(n); e=check(n,p)
        except AssertionError as ex:
            e=('assert',ex.args)
        if e: bad.append((n,e))
    print('bad count',len(bad)); print(bad[:40])
