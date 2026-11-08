import sys
def load(p):
    d={}
    for l in open(p,encoding='utf-8'):
        n,c,u,h=l.rstrip('\n').split('\t'); d[n]=(int(c),int(u),h)
    return d
L=load(sys.argv[1]);K=load(sys.argv[2])
common=[n for n in K if n in L]
same=[n for n in common if K[n]==L[n]]
diff=[n for n in common if K[n]!=L[n]]
print(f"lean {len(L)} kolla {len(K)} common {len(common)} identical {len(same)} differ {len(diff)}")
print("only in kolla:",len([n for n in K if n not in L]),[n for n in K if n not in L][:5])
sc=lambda ns,i,d:sum(d[n][i] for n in ns)
print(f"calls over common: lean {sc(common,0,L):,} kolla {sc(common,0,K):,}; unfolds: lean {sc(common,1,L):,} kolla {sc(common,1,K):,}")
print(f"calls over differing: lean {sc(diff,0,L):,} kolla {sc(diff,0,K):,}")
more=sorted(diff,key=lambda n:-(K[n][0]-L[n][0]))
print("kolla does most extra comparisons:")
for n in more[:12]: print(f"  {K[n][0]:>10,} vs {L[n][0]:>10,}  {n[:90]}")
print("kolla does fewest (lean more):")
for n in more[-5:]: print(f"  {K[n][0]:>10,} vs {L[n][0]:>10,}  {n[:90]}")
eqcount=[n for n in diff if K[n][:2]==L[n][:2]]
print("differ only in hash (same counts):",len(eqcount),eqcount[:5])
