"""E3. ¿Es el ángulo (alpha) o la palabra concreta? y ¿números nobles vs no nobles?
 (a) dorado con 12 fases rho al azar, N=45 y 60.
 (b) alpha = [0; a1..ak, cola], cola de 1s (nobles), de 2s o de 4s; prefijos al azar con a1>=2."""
import json, random, math
from palabras import rot, primitive
from correr import plano, toro
random.seed(7)
def cf(prefix, tail, depth=40):
    a=prefix+[tail]*depth; x=0.0
    for q in reversed(a): x=1/(q+x)
    return x
items=[]
for N in (45,60):
    for k in range(12):
        rho=random.random(); w=rot((3-5**0.5)/2,N,rho)
        if w[0]=='R' and primitive(w): items.append(dict(grupo='dorado_rho',N=N,alpha=(3-5**0.5)/2,rho=rho,w=w))
prefs=set()
while len(prefs)<40:
    k=random.randint(1,3); p=tuple([random.randint(2,6)]+[random.randint(1,4) for _ in range(k-1)])
    prefs.add(p)
for p in prefs:
    for tail,name in [(1,'noble'),(2,'cola2'),(4,'cola4')]:
        a=cf(list(p),tail)
        if not (0.05<a<0.5): continue
        for N in (45,60):
            w=rot(a,N)
            if primitive(w) and 'L' in w: items.append(dict(grupo=name,N=N,alpha=a,rho=0,w=w,pref=list(p)))
ws=[it['w'] for it in items]; print('reglas',len(set(ws)))
pl=plano(ws); tr=toro(ws)
for it in items: it.update(hw=pl[it['w']]['hw'],P=pl[it['w']]['P'],t100=tr[it['w']]['t100'])
json.dump(items,open('e3.json','w'))
