"""Predicción fuera de muestra: con m impar, ajusté P(RⁿLᵐ) = 16n + m² + 8m − 5 usando m=1,3,5.
Se prueba con m=7 y m=9, que no se usaron para el ajuste."""
from reglas_base import trajectory, highway
def norm(h):
    P, v, t = h
    k = 2 // max(abs(v[0]), abs(v[1])) if max(abs(v[0]), abs(v[1])) < 2 else 1
    return P * k
for m in (7, 9):
    hits, total = 0, 0
    for n in range(1, 21):
        h = highway(*trajectory("R" * n + "L" * m))
        if not h: continue
        P = norm(h); pred = 16 * n + m * m + 8 * m - 5
        total += 1; hits += P == pred
        print(f"m={m} n={n:2d}  observado={P:4d}  predicho={pred:4d}  {'✓' if P == pred else '✗'}")
    print(f"m={m}: {hits}/{total} aciertos\n")
