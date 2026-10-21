"""E1 (confirmatorio). Predicciones fijadas antes de correr, para N = 13..60 (datos no vistos):
 P1: las reglas de Fibonacci (rotación por 1/phi^2) no forman autopista en 5e6 pasos.
 P2: en el toro 128x128 cubren antes que la mediana de las reglas balanceadas de rotación con
     alpha al azar del mismo N (prueba de signo sobre los N)."""
import json, random
from palabras import *
from correr import plano, toro
random.seed(20261021)
R={}
for N in range(13,61):
    g=rot(ALPHAS['dorado'],N)
    items=[('dorado',g)]
    for k in ('plata','bronce'): items.append((k,rot(ALPHAS[k],N)))
    seen=set()
    while len([1 for c,_ in items if c=='azar'])<30:
        a=random.uniform(0.05,0.5); w=rot(a,N)
        if w not in seen and 'L' in w: seen.add(w); items.append(('azar',w))
    seen=set()
    while len([1 for c,_ in items if c=='barajada'])<15:
        l=list(g); random.shuffle(l); w=''.join(l)
        if w[0]=='R' and w not in seen: seen.add(w); items.append(('barajada',w))
    items.append(('bloque','R'*g.count('R')+'L'*g.count('L')))
    R[N]=[(c,w) for c,w in items if primitive(w)]
rules=[w for N in R for c,w in R[N]]
print('reglas distintas:',len(set(rules)))
pl=plano(rules); print('plano listo'); tr=toro(rules); print('toro listo')
json.dump(dict(R={str(k):v for k,v in R.items()},plano=pl,toro=tr),open('e1.json','w'))
