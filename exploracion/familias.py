"""Verifica la ley del periodo en familias de reglas RⁿL y RⁿLLL (y otras) más allá de 9 colores."""
from reglas_base import trajectory, highway
def norm(h):
    # un periodo P con desplazamiento (±1,±1) equivale a 2P con (±2,±2)
    P, v, t = h
    k = 2 // max(abs(v[0]), abs(v[1])) if max(abs(v[0]), abs(v[1])) < 2 else 1
    return P * k, (v[0] * k, v[1] * k), t
for tail in ("L", "LLL", "LLLLL", "LL"):
    print(f"Familia R^n{tail}:")
    for n in range(1, 17):
        rule = "R" * n + tail
        if len(rule) < 2: continue
        h = highway(*trajectory(rule))
        if h: P, v, t = norm(h); print(f"   n={n:2d} {rule:22s} periodo={P:4d}  desplazamiento={v}  caos={t}")
        else: print(f"   n={n:2d} {rule:22s} sin autopista en 3M pasos")
