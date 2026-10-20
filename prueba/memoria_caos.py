"""¿El caos de la hormiga RL es una búsqueda sin memoria? Para miles de tableros iniciales al azar
(finitos), se mide el paso T en que empieza la autopista (certificado por el núcleo en C) y se
estudia la cola de la distribución: si es exponencial, la espera no tiene memoria."""
import sys, random, math
sys.path.insert(0, "..")
import numpy as np
from scipy import stats
import antlib as A
rng = random.Random(20261020)
def muestra(k, p, nmuestras):
    Ts, dens = [], []
    for _ in range(nmuestras):
        cells = [(x, y) for x in range(-(k // 2), k // 2 + 1) for y in range(-(k // 2), k // 2 + 1) if rng.random() < p]
        r = A.run(cells, maxsteps=3_000_000)
        if r["ok"]: Ts.append(r["T"]); dens.append(len(cells))
    return np.array(Ts), np.array(dens)
for k, p, M in [(5, 0.5, 4000), (9, 0.5, 2000), (15, 0.3, 1000)]:
    T, dn = muestra(k, p, M)
    print(f"\n== tableros {k}×{k} al azar (densidad {p}), {len(T)} de {M} con autopista certificada")
    print(f"   T: mínimo {T.min():,}  mediana {int(np.median(T)):,}  media {int(T.mean()):,}  máximo {T.max():,}")
    # memoria: E[T - a | T > a] para varios umbrales a
    for q in (0.25, 0.5, 0.75, 0.9):
        a = np.quantile(T, q); exc = T[T > a] - a
        print(f"   pasado el cuantil {q:.2f} (a = {int(a):,}): espera media restante {int(exc.mean()):,}  desviación {int(exc.std()):,}  (n = {len(exc)})")
    a = np.quantile(T, 0.5); exc = T[T > a] - a
    ks = stats.kstest(exc, "expon", args=(0, exc.mean()))
    print(f"   prueba de Kolmogorov-Smirnov contra exponencial (mitad superior): p = {ks.pvalue:.3f}")
    rho = stats.spearmanr(dn, T)
    print(f"   correlación entre número de casillas negras iniciales y T: rho = {rho.statistic:.3f} (p = {rho.pvalue:.2g})")
