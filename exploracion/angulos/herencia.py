"""Herencia por prefijo. Lema (trivial): si la trayectoria de u desde el blanco nunca visita una casilla
más de K_u veces, toda regla w con w[c mod N] = u[c mod q] para c < K_u tiene exactamente la misma
trayectoria (cada casilla lee los mismos estados en el mismo orden). Aquí: ¿qué fracción de las
autopistas del catálogo (2-12 estados) se hereda así de una regla más corta?"""
import json, itertools, collections
from palabras import primitive
from correr import plano
hw=json.load(open('../pendientes.json'))
small={w:v for w,v in hw.items() if primitive(w)}
pl=plano(list(small),T=5_000_000)
json.dump(pl,open('K_catalogo.json','w'))
def agrees(w,u,K):
    N,q=len(w),len(u); return all(w[c%N]==u[c%q] for c in range(K))
rules=[]
for N in range(2,13):
    for b in itertools.product('RL',repeat=N-1):
        w='R'+''.join(b)
        if 'L' in w and primitive(w): rules.append(w)
pred={}; 
for w in rules:
    for u in sorted(small,key=len):
        if len(u)>=len(w): break
        if agrees(w,u,pl[u]['K']): pred[w]=u; break
ok=bad=0; inh=collections.Counter(); tot=collections.Counter()
for w in rules:
    if w in hw: tot[len(w)]+=1
    if w in pred:
        u=pred[w]; v=hw.get(w)
        same = v is not None and v['P']==hw[u]['P'] and list(v['v'])==list(hw[u]['v']) and v['inicio']==hw[u]['inicio']
        ok+=same; bad+= not same
        if same: inh[len(w)]+=1
        elif bad<=5: print('MISMATCH',w,u,v,hw[u])
print(f'predicciones por herencia: {ok+bad}; correctas (misma P, desplazamiento e inicio): {ok}; fallidas: {bad}')
print('autopistas por N: total / heredadas / nuevas')
for N in range(2,13): print(f'  {N:2d}: {tot[N]:4d} {inh[N]:4d} {tot[N]-inh[N]:4d}')
print('total', sum(tot.values()), sum(inh.values()))
print('K de algunas reglas:', {u:pl[u]['K'] for u in ['RL','RRL','RRRL','RRRRL','RLL' if 'RLL' in pl else 'RL']})
