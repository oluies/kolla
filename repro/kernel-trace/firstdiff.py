import sys,re
from collections import Counter
def load(p):
    d={};cur=None
    for l in open(p,encoding='utf-8',errors='replace'):
        l=l.rstrip('\n')
        if l.startswith('@ '): cur=l[2:]; d[cur]=[]
        elif cur: d[cur].append(l)
    return d
L=load(sys.argv[1]);K=load(sys.argv[2])
g=Counter();ex={}
same=0
for n in K:
    if n not in L: continue
    a,b=L[n],K[n]
    i=0
    while i<len(a) and i<len(b) and a[i]==b[i]: i+=1
    if i==len(a) and i==len(b): same+=1; continue
    x=a[i] if i<len(a) else '<end>'; y=b[i] if i<len(b) else '<end>'
    norm=lambda s:re.sub(r'^\d+ ','',s)
    def shape(s):
        s=norm(s)
        s=re.sub(r'/\d+','',s)
        if s.startswith('U '): return 'U'
        if s.startswith('< '): return '< r'
        return s
    key=(shape(x)[:70],shape(y)[:70])
    g[key]+=1
    ex.setdefault(key,(n,i,x,y))
print("compared",len([n for n in K if n in L]),"identical",same)
for k,c in g.most_common(14):
    n,i,x,y=ex[k]
    print(f"{c:5}  LEAN {k[0]!r}\n       KOLLA {k[1]!r}\n       e.g. {n[:70]} at {i}: {x[:80]!r} / {y[:80]!r}")
