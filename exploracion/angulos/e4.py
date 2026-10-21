"""E4. Escalamiento del tiempo de cobertura del toro n x n (n = 32..512):
autopista temprana vs caóticas (catálogo 2-12 estados), más RL y Fibonacci."""
import json, random, itertools
from palabras import primitive, rot, ALPHAS
from correr import toro
random.seed(3)
hw=json.load(open('../pendientes.json'))
allr=['R'+''.join(b) for N in range(2,13) for b in itertools.product('RL',repeat=N-1)]
allr=[w for w in allr if 'L' in w and primitive(w)]
fast=random.sample([w for w in allr if w in hw and hw[w]['inicio']<1000],60)
cha=random.sample([w for w in allr if w not in hw],60)
extra=['RL','RRL','RRRL',rot(ALPHAS['dorado'],13),rot(ALPHAS['dorado'],34),rot(ALPHAS['plata'],34)]
rules=fast+cha+extra
res={}
for n in (32,64,128,256,512):
    res[n]=toro(rules,n=n,T=400*n*n); print('n',n,'listo',flush=True)
json.dump(dict(fast=fast,cha=cha,extra=extra,res=res),open('e4.json','w'))
