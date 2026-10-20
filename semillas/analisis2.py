"""Versión entrópica de la hipótesis: la información de la semilla se mide con la estadística real del caos.
Para cada regla, se toma una foto del caos (a la mitad del transitorio desde el blanco), se miden las
frecuencias q(c) de cada color dentro de la mancha, y la información de la semilla es
    I = − Σ_{casillas de la caja de la semilla} log2 q(color de esa casilla en la semilla).
Además se mide la entropía por casilla del caos, H = − Σ q log2 q."""
import json, math
import numpy as np
from scipy import stats
import azar as Z

R = json.load(open("resultados_semillas.json"))
rows = []
for rule, s in R.items():
    Ks = np.array(s["Ks"], float)
    if len(Ks) < 50 or len(Ks) < 0.9 * (len(Ks) + s["fallos"]): continue
    N = s["N"]
    # frecuencias de colores en el caos (foto a la mitad del transitorio desde el blanco)
    foto = Z.correr(rule, snap_t=max(1, s["T0"] // 2), snap_r=400)["foto"]
    if len(foto) < 20: continue
    xs = [c[0] for c in foto]; ys = [c[1] for c in foto]
    area = (max(xs) - min(xs) + 1) * (max(ys) - min(ys) + 1)
    cnt = np.zeros(N);
    for c in foto: cnt[c[2]] += 1
    cnt[0] = area - len(foto)
    q = (cnt + 0.5) / (cnt.sum() + 0.5 * N)          # suavizado para colores raros
    H = float(-(q * np.log2(q)).sum())
    seed = {(c[0], c[1]): c[2] for c in s["semilla"]}
    sx = [p[0] for p in seed] or [0]; sy = [p[1] for p in seed] or [0]
    I = 0.0
    for x in range(min(sx), max(sx) + 1):
        for y in range(min(sy), max(sy) + 1):
            I += -math.log2(q[seed.get((x, y), 0)])
    Inz = sum(-math.log2(q[c]) for c in seed.values())
    rows.append(dict(rule=rule, N=N, P=s["P"], k=s["k"], H=H, I=I, Inz=Inz, espera=Ks.mean()))
print(f"reglas analizadas: {len(rows)}")
y = np.log2([r["espera"] for r in rows])
for name, lab in (("I", "información de la caja de la semilla (con estadística del caos)"),
                  ("Inz", "información solo de las casillas no nulas de la semilla"),
                  ("H", "entropía por casilla del caos"), ("k", "casillas de la semilla"), ("N", "colores")):
    x = np.array([r[name] for r in rows], float)
    rho = stats.spearmanr(x, y)
    print(f"   {lab:62s} rho = {rho.statistic:+.3f}  p = {rho.pvalue:.2g}")
for name in ("I", "Inz"):
    x = np.array([r[name] for r in rows], float)
    lr = stats.linregress(x, y)
    print(f"   regresión log2(espera) vs {name}: pendiente {lr.slope:.3f} ± {lr.stderr:.3f}, R² = {lr.rvalue**2:.3f}")
json.dump(rows, open("tabla_entropica.json", "w"), indent=0)
