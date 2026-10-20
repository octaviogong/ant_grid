"""Misma pregunta, pero midiendo el tiempo en 'casillas nuevas visitadas' en lugar de pasos."""
import sys, random
sys.path.insert(0, "..")
import numpy as np
from scipy import stats
import antlib as A
rng = random.Random(7)
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
def nuevas_hasta(cells, T):
    B = set(cells); x = y = 0; d = 0; vis = {(0, 0)}
    for _ in range(T):
        c = (x, y) in B
        d = (d + 3) % 4 if c else (d + 1) % 4
        B ^= {(x, y)}; x += D[d][0]; y += D[d][1]; vis.add((x, y))
    return len(vis)
Ts, Ks = [], []
for _ in range(3000):
    cells = [(x, y) for x in range(-2, 3) for y in range(-2, 3) if rng.random() < 0.5]
    r = A.run(cells, maxsteps=3_000_000)
    if r["ok"]: Ts.append(r["T"]); Ks.append(nuevas_hasta(cells, r["T"]))
T, K = np.array(Ts), np.array(Ks)
print(f"{len(K)} tableros 5×5. Casillas distintas visitadas al empezar la autopista: mediana {int(np.median(K))}, media {int(K.mean())}")
for name, X in (("pasos", T), ("casillas nuevas", K)):
    print(f"\n   midiendo en {name}:")
    for q in (0.25, 0.5, 0.75, 0.9):
        a = np.quantile(X, q); exc = X[X > a] - a
        print(f"      pasado el cuantil {q:.2f}: espera media restante {exc.mean():8.0f}   desviación {exc.std():8.0f}")
    exc = X[X > np.quantile(X, 0.5)] - np.quantile(X, 0.5)
    print(f"      K-S contra exponencial (mitad superior): p = {stats.kstest(exc, 'expon', args=(0, exc.mean())).pvalue:.3f}")
# relación entre pasos y casillas: crecimiento de la mancha
b = np.polyfit(np.log(K), np.log(T), 1)
print(f"\n   pasos ≈ casillas^{b[0]:.2f}  (si la mancha fuera un camino aleatorio en 2D, el exponente sería cercano a 1 con correcciones logarítmicas)")
