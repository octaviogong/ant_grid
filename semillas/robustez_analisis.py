"""Análisis de robustez: falta de memoria en la cola, estabilidad de la tasa entre condiciones
iniciales, y la ley semilla–espera en cada condición."""
import json, math
import numpy as np
from scipy import stats
R = json.load(open("robustez.json"))
S = json.load(open("resultados_semillas.json"))
C = ("A", "B", "C")
nombre = {"A": "5×5 denso", "B": "9×9 al 30%", "C": "15×15 al 10%"}
def cola(x):
    x = np.sort(np.asarray(x, float)); med = np.median(x); exc = x[x > med] - med
    q25, q75 = np.quantile(x, 0.25), np.quantile(x, 0.75)
    mrl = lambda a: (x[x > a] - a).mean()
    return exc.std() / exc.mean(), mrl(q75) / mrl(q25)
rows = []
for rule, d in R.items():
    row = dict(rule=rule, N=len(rule), k=S[rule]["k"], P=S[rule]["P"])
    for c in C:
        K, T = d[c]["Ks"], d[c]["Ts"]
        if len(K) < 300: row[c] = None; continue
        cvK, mrlK = cola(K); cvT, mrlT = cola(T)
        row[c] = dict(media=float(np.mean(K)), cv=float(np.std(K) / np.mean(K)), cv_cola=cvK, mrl=mrlK,
                      cv_cola_T=cvT, mrl_T=mrlT, exito=len(K) / 400)
    rows.append(row)
ok = [r for r in rows if all(r[c] for c in C)]
print(f"reglas con las tres condiciones bien medidas: {len(ok)} de {len(rows)}")
print("\n1) Falta de memoria en la cola (exponencial → CV de la cola = 1, cociente de vida residual = 1):")
for c in C:
    cvc = [r[c]["cv_cola"] for r in ok]; mr = [r[c]["mrl"] for r in ok]
    cvt = [r[c]["cv_cola_T"] for r in ok]; mrt = [r[c]["mrl_T"] for r in ok]
    print(f"   {nombre[c]:13s} en casillas: CV cola mediana {np.median(cvc):.2f} [{np.quantile(cvc,.25):.2f}–{np.quantile(cvc,.75):.2f}], "
          f"vida residual q75/q25 mediana {np.median(mr):.2f}   |  en pasos: CV cola {np.median(cvt):.2f}, vida residual {np.median(mrt):.2f}")
largos = [r for r in ok if r["A"]["media"] >= 1000]
print(f"\n   solo reglas con espera ≥ 1 000 casillas ({len(largos)}):")
for c in C:
    print(f"   {nombre[c]:13s} CV total mediana {np.median([r[c]['cv'] for r in largos]):.2f}, CV cola {np.median([r[c]['cv_cola'] for r in largos]):.2f}, "
          f"vida residual {np.median([r[c]['mrl'] for r in largos]):.2f}")
print("\n2) ¿La tasa es propia de cada regla? (misma regla, distinto tablero inicial)")
la = np.log2([r["A"]["media"] for r in ok])
for c in ("B", "C"):
    lc = np.log2([r[c]["media"] for r in ok])
    rho = stats.spearmanr(la, lc).statistic
    ratio = np.array([r[c]["media"] / r["A"]["media"] for r in ok])
    ratio_l = np.array([r[c]["media"] / r["A"]["media"] for r in largos])
    print(f"   A vs {c}: Spearman {rho:.3f}; cociente de esperas mediana {np.median(ratio):.2f} "
          f"(en reglas de espera larga: {np.median(ratio_l):.2f}, rango {ratio_l.min():.2f}–{ratio_l.max():.2f})")
print("\n3) Ley semilla–espera en cada condición:")
for c in C:
    k = np.array([r["k"] for r in ok], float); y = np.log2([r[c]["media"] for r in ok])
    rho = stats.spearmanr(k, y); lr = stats.linregress(np.log2(k), y)
    print(f"   {nombre[c]:13s} Spearman {rho.statistic:+.3f} (p = {rho.pvalue:.2g}); espera ∝ semilla^{lr.slope:.2f} ± {lr.stderr:.2f}, R² = {lr.rvalue**2:.2f}")
json.dump(rows, open("robustez_tabla.json", "w"), indent=0)
