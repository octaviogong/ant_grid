import json, statistics as st, collections
from scipy.stats import binomtest, mannwhitneyu
D=json.load(open('e1.json')); R=D['R']; pl=D['plano']; tr=D['toro']; n2=128*128
INF=float('inf')
def cov(w): t=tr[w]['t100']; return t/n2 if t>=0 else INF
cls=collections.defaultdict(list)
for N,items in R.items():
    for c,w in items: cls[c].append((int(N),w))
print('clase       reglas  autopista%   nunca cubre%   mediana t100 (n^2)')
for c in ['dorado','plata','bronce','azar','barajada','bloque']:
    v=cls[c]; h=sum(pl[w]['hw'] for N,w in v); nc=sum(cov(w)==INF for N,w in v)
    print(f'{c:10s} {len(v):6d}   {100*h/len(v):6.1f}      {100*nc/len(v):6.1f}        {st.median(cov(w) for N,w in v):6.1f}')
print('\nP1 golden highways:',[(N,pl[w]['P'],pl[w]['inicio']) for N,w in cls['dorado'] if pl[w]['hw']])
# P2: sign test, golden vs median of random-alpha balanced of same N
wins=0; tot=0; rows=[]
for N,items in R.items():
    g=[w for c,w in items if c=='dorado']
    if not g: continue
    ctrl=[cov(w) for c,w in items if c=='azar']
    m=st.median(ctrl); x=cov(g[0]); tot+=1; wins+= x<m
    rows.append((int(N),x,m))
print(f'P2: golden faster than random-alpha median in {wins}/{tot} lengths; sign test p = {binomtest(wins,tot,0.5,alternative="greater").pvalue:.3g}')
for k in ('plata','bronce'):
    w2=sum(cov(w)< st.median(cov(u) for c,u in R[str(N)] if c=='azar') for N,w in cls[k])
    print(f'   {k}: faster than median in {w2}/{len(cls[k])}; p = {binomtest(w2,len(cls[k]),0.5,alternative="greater").pvalue:.3g}')
# golden vs shuffles of same letters
w3=sum(cov(w)< st.median(cov(u) for c,u in R[str(N)] if c=='barajada') for N,w in cls['dorado'])
print(f'   golden faster than median of its own shuffles in {w3}/{len(cls["dorado"])}')
print('\nper N (N, golden t100, random-alpha median):'); print([(N,round(x,1),round(m,1)) for N,x,m in sorted(rows)])
