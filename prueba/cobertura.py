"""Cobertura exacta: cada (n, j) con j >= 2, n >= 2j debe caer en exactamente una pieza."""
import json, sys
from fractions import Fraction as Fr
def member(p, n, j):
    (a, b, c), (d, e, f) = p["n"], p["j"]
    N, J = n - a, j - d
    used_x = b != 0 or e != 0; used_y = c != 0 or f != 0
    if not used_x and not used_y: return N == 0 and J == 0
    if used_x and not used_y:
        sols = set()
        if b: x = Fr(N, b)
        else: x = Fr(J, e)
        return x.denominator == 1 and x >= 0 and b * x == N and e * x == J
    if used_y and not used_x:
        y = Fr(N, c) if c else Fr(J, f)
        return y.denominator == 1 and y >= 0 and c * y == N and f * y == J
    det = b * f - c * e
    if det == 0: raise RuntimeError("pieza degenerada")
    x = Fr(N * f - c * J, det); y = Fr(b * J - e * N, det)
    return x.denominator == 1 and y.denominator == 1 and x >= 0 and y >= 0
pieces = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "parteA_piezas.json"))
holes, overl, total = [], [], 0
for j in range(2, 80):
    for n in range(2 * j, 2 * j + 300):
        k = [i for i, p in enumerate(pieces) if member(p, n, j)]
        total += 1
        if not k: holes.append((n, j))
        elif len(k) > 1: overl.append((n, j, k))
print(f"puntos: {total}  huecos: {len(holes)}  traslapes: {len(overl)}")
print(holes[:12], overl[:6])
