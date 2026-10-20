"""Todas las reglas (distintas salvo simetría) en 3D (2-5 colores) y 4D (2-4 colores), desde vacío."""
import json, time, sys
import numpy as np
import antnd as A
MAXS = 20_000_000
res = []
t0 = time.time()
for d, nmax in ((3, 5), (4, 4)):
    for n in range(2, nmax + 1):
        for rule in A.canonical_rules(d, n):
            if len(set(rule)) == 1: continue          # un solo giro: gira en un cuadrito para siempre
            T = A.run(rule, d, MAXS)
            h = A.highway(T)
            rmax = float(np.max(np.abs(T[-200000:])))
            row = dict(d=d, n=n, regla=rule, dim_efectiva=A.eff_dim(rule), pasos=len(T) - 1,
                       tipo=h["tipo"] if h else "sin patrón", P=h["P"] if h else None,
                       v=h["v"] if h else None, inicio=h["inicio"] if h else None,
                       clase=A.direction_class(h["v"]) if h and h["tipo"] == "autopista" else None,
                       alcance_final=rmax)
            res.append(row)
            print(json.dumps(row, ensure_ascii=False)); sys.stdout.flush()
json.dump(res, open("dimensiones.json", "w"), ensure_ascii=False, indent=0)
print(f"[{time.time()-t0:.0f}s]")
