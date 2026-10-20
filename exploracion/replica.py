"""Réplica fuera de muestra de la única señal que sobrevivió: par (p,q) vs periodo de p/q.
Los pares comparten denominador q, así que la unidad independiente es q:
prueba de permutación por bloques (se barajan los invariantes entre los q, no entre pares)."""
import math, random
import numpy as np
from scipy import stats
import antlib as A, codif as E
rng = random.Random(11)
def experiment(primes_list, label):
    T, prop, qs = [], [], []
    for i, p in enumerate(primes_list):
        for q in primes_list[i+1:]:
            T.append(A.run(E.enc_par(p, q)[0])["T"]); qs.append(q)
            prop.append(E.period(p, q, 2)[1] / (q - 1))
    obs = stats.spearmanr(prop, T).statistic
    uq = sorted(set(qs)); val = {q: E.mult_order(2, q) / (q - 1) for q in uq}
    perm = []
    for _ in range(5000):
        sh = rng.sample([val[q] for q in uq], len(uq)); m = dict(zip(uq, sh))
        perm.append(stats.spearmanr([m[q] for q in qs], T).statistic)
    p_block = float(np.mean(np.abs(perm) >= abs(obs)))
    # agregado por q: mediana de log T por denominador
    agg = [(val[q], np.median([math.log10(t+1) for t, qq in zip(T, qs) if qq == q])) for q in uq if qs.count(q) >= 3]
    ra = stats.spearmanr(*zip(*agg))
    print(f"{label}: pares={len(T)} denominadores={len(uq)} rho={obs:.3f}  p_bloques={p_block:.3f}  "
          f"rho_agregado_por_q={ra.statistic:.3f} (p={ra.pvalue:.3f}, n={len(agg)})")
P = [p for p in E.primes(2000) if p > 2]
experiment(P[:25], "Original  (primos 3..101)  ")
experiment(P[25:50], "Réplica 1 (primos 103..233)")
experiment(P[50:75], "Réplica 2 (primos 239..389)")
experiment(P[75:100], "Réplica 3 (primos 397..547)")
