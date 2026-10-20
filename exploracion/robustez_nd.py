"""La 'conjetura' en dimensión alta: para reglas genuinamente 3D/4D, ¿todo tablero inicial
pequeño al azar termina en el mismo patrón que el tablero vacío?"""
import json, random
from collections import Counter
import numpy as np
import antnd as A
rng = random.Random(3)
MAXS = 5_000_000
rows = json.load(open("dimensiones.json", encoding="utf-8"))
genuine = [r for r in rows if r["dim_efectiva"] == r["d"]]
pick = [r for r in genuine if r["tipo"] == "autopista"][:10] + [r for r in genuine if r["tipo"] == "ciclo"][:6]
out = []
for r in pick:
    d, rule, n = r["d"], r["regla"], r["n"]
    res = Counter(); same = 0
    for _ in range(30):
        init = []
        for cell in np.ndindex(*(3,) * d):
            if rng.random() < 0.5: init.append((tuple(int(c) - 1 for c in cell), rng.randrange(1, n)))
        T = A.run(rule, d, MAXS, init=init)
        h = A.highway(T)
        if h is None: res["sin patrón"] += 1
        elif h["tipo"] == "ciclo": res[f"ciclo P={h['P']}"] += 1
        else:
            res[f"autopista P={h['P']} clase={A.direction_class(h['v'])}"] += 1
            same += h["P"] == r["P"]
    vacio = f"{r['tipo']} P={r['P']}" + (f" clase={tuple(r['clase'])}" if r["clase"] else "")
    out.append(dict(d=d, regla=rule, desde_vacio=vacio, desde_azar=dict(res), misma_autopista=same))
    print(json.dumps(out[-1], ensure_ascii=False), flush=True)
json.dump(out, open("robustez_nd.json", "w"), ensure_ascii=False, indent=1)
