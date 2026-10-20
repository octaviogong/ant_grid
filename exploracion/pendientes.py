"""¿Qué pendientes (qué 'nudos') tienen las autopistas? Reglas de 2 a 12 colores, tablero blanco."""
import itertools, json
from math import gcd
from reglas_base import trajectory, highway
from collections import Counter
res = {}
for L in range(2, 13):
    for tail in itertools.product("LR", repeat=L - 1):
        rule = "R" + "".join(tail)
        if set(rule) == {"R"}: continue
        h = highway(*trajectory(rule))
        if h: res[rule] = dict(P=int(h[0]), v=[int(h[1][0]), int(h[1][1])], inicio=int(h[2]))
pend = Counter()
for r, v in res.items():
    dx, dy = v["v"]; g = gcd(abs(dx), abs(dy))
    pend[(abs(dx) // g, abs(dy) // g)] += 1
print("reglas probadas:", 2**12 - 1 - 11, " con autopista:", len(res))
print("clases de pendiente |dx|:|dy| reducidas:", dict(pend))
nodiag = {r: v for r, v in res.items() if abs(v["v"][0]) != abs(v["v"][1])}
print("autopistas no diagonales:", len(nodiag))
for r, v in list(nodiag.items())[:30]: print("  ", r, v)
json.dump(res, open("pendientes.json", "w"), indent=0)
