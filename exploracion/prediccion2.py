"""Segunda predicción fuera de muestra. Ley ajustada con m=3,5,7,9:
P(RⁿLᵐ) = 16·(n+m) − 20 para m impar ≥ 3 (y 16·(n+1) − 12 para m=1, n≥2).
Se prueba con m=11 y m=13, que no se usaron."""
from reglas_base import trajectory, highway
def norm(h):
    P, v, t = h
    k = 2 // max(abs(v[0]), abs(v[1])) if max(abs(v[0]), abs(v[1])) < 2 else 1
    return P * k
for m in (11, 13):
    hits, total, miss = 0, 0, []
    for n in range(1, 25):
        h = highway(*trajectory("R" * n + "L" * m))
        if not h: continue
        P = norm(h); pred = 16 * (n + m) - 20
        total += 1; hits += P == pred
        if P != pred: miss.append((n, P, pred))
    print(f"m={m}: {hits}/{total} aciertos (n con autopista: {total}); fallos={miss}")
