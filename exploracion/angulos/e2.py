"""E2. Diagrama de fases sobre el ángulo: N fijo, alpha en (0.01, 0.5), regla = rotación por alpha.
Para cada palabra distinta: autopista (plano, 5e6 pasos), herencia desde el catálogo, cobertura del toro 128."""
import json, numpy as np
from palabras import rot, primitive
from correr import plano, toro
hw=json.load(open('../pendientes.json')); Kc=json.load(open('K_catalogo.json'))
small=sorted(Kc,key=len)
def agrees(w,u,K):
    N,q=len(w),len(u); return all(w[c%N]==u[c%q] for c in range(K))
def source(w):
    for u in small:
        if len(u)<len(w) and agrees(w,u,Kc[u]['K']): return u
    return None
out={}
for N in (30,60):
    alphas=np.arange(0.01,0.5,0.0002); words={}
    for a in alphas:
        w=rot(a,N)
        if 'L' in w and primitive(w): words.setdefault(w,[]).append(float(a))
    ws=list(words); print(N,'palabras distintas',len(ws))
    pl=plano(ws); tr=toro(ws)
    out[N]=[dict(w=w,amin=min(words[w]),amax=max(words[w]),hw=pl[w]['hw'],P=pl[w]['P'],d=pl[w]['d'],inicio=pl[w]['inicio'],
                 K=pl[w]['K'],src=source(w),t100=tr[w]['t100'],t90=tr[w]['t90']) for w in ws]
# fuente de herencia incluyendo toda la familia RⁿL (K = 2n+2, del teorema de herencia)
fuentes={u:Kc[u]['K'] for u in Kc}
for n in range(2,61): fuentes['R'*n+'L']=2*n+2
orden=sorted(fuentes,key=len)
for N in out:
    for r in out[N]:
        r['src2']=next((u for u in orden if len(u)<len(r['w']) and agrees(r['w'],u,fuentes[u])),None)
json.dump(out,open('e2.json','w'))
