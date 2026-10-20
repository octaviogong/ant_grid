"""Análisis: ¿la información de la semilla predice la espera?"""
import json, math
import numpy as np
from scipy import stats

R = json.load(open("resultados_semillas.json"))
rows = []
for rule, s in R.items():
    Ks = np.array(s["Ks"], float)
    if len(Ks) < 0.9 * (len(Ks) + s["fallos"]) or len(Ks) < 50:
        continue
    N = s["N"]
    rows.append(dict(rule=rule, N=N, P=s["P"], k=s["k"], area=s["area"],
                     bits_k=s["k"] * math.log2(N), bits_area=s["area"] * math.log2(N),
                     espera=Ks.mean(), cv=Ks.std() / Ks.mean(), K0=s["K0"], exito=len(Ks) / (len(Ks) + s["fallos"])))
print(f"reglas con espera bien medida (≥ 90% de éxitos): {len(rows)} de {len(R)}")
y = np.log2([r["espera"] for r in rows])

def resid(v, Z):
    X = np.column_stack([np.ones(len(v))] + Z)
    return v - X @ np.linalg.lstsq(X, v, rcond=None)[0]

print("\nCorrelación de Spearman entre log2(espera media en casillas) y cada medida de la semilla:")
for name in ("k", "bits_k", "area", "bits_area", "N", "P"):
    x = np.array([r[name] for r in rows], float)
    rho = stats.spearmanr(x, y)
    print(f"   {name:10s} rho = {rho.statistic:+.3f}   p = {rho.pvalue:.2g}")

print("\nControlando por número de colores N y periodo P (correlación parcial de rangos):")
rk = lambda v: stats.rankdata(v)
Zc = [rk([r["N"] for r in rows]), rk([math.log(r["P"]) for r in rows])]
for name in ("k", "bits_k", "area", "bits_area"):
    x = np.array([r[name] for r in rows], float)
    a, b = resid(rk(x), Zc), resid(rk(y), Zc)
    rr = stats.pearsonr(a, b)
    print(f"   {name:10s} rho parcial = {rr.statistic:+.3f}   p = {rr.pvalue:.2g}")

print("\nRegresión log2(espera) = a + b·bits_k:")
x = np.array([r["bits_k"] for r in rows])
lr = stats.linregress(x, y)
print(f"   pendiente b = {lr.slope:.3f} ± {lr.stderr:.3f}   ordenada a = {lr.intercept:.2f}   R² = {lr.rvalue**2:.3f}")
print("   (la hipótesis «espera ≈ 2^bits» predice pendiente 1)")

cv = np.array([r["cv"] for r in rows])
print(f"\nSin memoria: coeficiente de variación de la espera por regla (exponencial → 1): mediana {np.median(cv):.2f}, "
      f"cuartiles {np.quantile(cv, 0.25):.2f}–{np.quantile(cv, 0.75):.2f}")

y0 = np.log2([r["K0"] for r in rows])
print(f"Espera desde el tablero en blanco vs espera media al azar: rho = {stats.spearmanr(y0, y).statistic:+.3f}")

rows.sort(key=lambda r: r["espera"])
print("\nEjemplos (de menor a mayor espera):")
for r in rows[:5] + rows[len(rows)//2 - 2: len(rows)//2 + 2] + rows[-5:]:
    print(f"   {r['rule']:13s} N={r['N']:2d} P={r['P']:5d} semilla={r['k']:4d} ({r['bits_k']:6.1f} bits)  espera={r['espera']:9.0f} ({math.log2(r['espera']):5.1f} bits)  cv={r['cv']:.2f}")
json.dump(rows, open("tabla_semillas.json", "w"), indent=0)
