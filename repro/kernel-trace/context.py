import sys
n=sys.argv[3]; i=int(sys.argv[4]); w=int(sys.argv[5]) if len(sys.argv)>5 else 12
def get(p):
    on=False;o=[]
    for l in open(p,encoding='utf-8',errors='replace'):
        l=l.rstrip('\n')
        if l.startswith('@ '):
            if on: break
            on=(l[2:]==n); continue
        if on: o.append(l)
    return o
a,b=get(sys.argv[1]),get(sys.argv[2])
print("--- common before");print('\n'.join(a[max(0,i-w):i]))
print("--- LEAN");print('\n'.join(a[i:i+w]))
print("--- KOLLA");print('\n'.join(b[i:i+w]))
