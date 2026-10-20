"""Verificación independiente de la Parte A:
1) cobertura: cada (n, j) de una caja grande pertenece a exactamente una pieza;
2) cada periodo simbólico, evaluado en el punto, pasa el certificado de repetición en una
   simulación concreta con enteros (código de certificado.py, sin el motor simbólico)."""
import json
from simbolico import Cone
from parteA import H
pieces = json.load(open("parteA_piezas.json"))
from fractions import Fraction as Fr
def members(p, n, j):
    (a, b, c), (d, e, f) = p["n"], p["j"]
    N, J = n - a, j - d
    ux = b != 0 or e != 0; uy = c != 0 or f != 0
    if not ux and not uy: return [(0, 0)] if (N == 0 and J == 0) else []
    if ux and not uy:
        x = Fr(N, b) if b else Fr(J, e)
        return [(int(x), 0)] if x.denominator == 1 and x >= 0 and b * x == N and e * x == J else []
    if uy and not ux:
        y = Fr(N, c) if c else Fr(J, f)
        return [(0, int(y))] if y.denominator == 1 and y >= 0 and c * y == N and f * y == J else []
    det = b * f - c * e
    x = Fr(N * f - c * J, det); y = Fr(b * J - e * N, det)
    return [(int(x), int(y))] if x.denominator == 1 and y.denominator == 1 and x >= 0 and y >= 0 else []
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
def concrete_certificate(n, j, P):
    m = 2 * j + 1; N = n + m
    R = Cone((n, 0, 0), (j, 0, 0)); B = {c: v[0] for c, v in H(R).items() if v[0]}
    x = y = 0; d = 2; start = (dict(B), (0, 0), 2); V = set()
    # periodo P desde H (t1 = 0) o, si la semilla aún no está en fase, desde t1 = P
    hist = []
    for t1 in (0, P, 2 * P):
        pass
    def run(B, x, y, d, steps):
        V = set()
        for _ in range(steps):
            V.add((x, y)); c = B.get((x, y), 0)
            d = (d + 1) % 4 if c < n else (d + 3) % 4
            c = (c + 1) % N
            if c: B[(x, y)] = c
            else: B.pop((x, y), None)
            x += D[d][0]; y += D[d][1]
        return B, x, y, d, V
    B0 = dict(B); x0, y0, d0 = 0, 0, 2
    for k in range(12):  # probar t1 = 0, P, 2P, ...
        B1 = dict(B0)
        B2, x2, y2, d2, V = run(dict(B1), x0, y0, d0, P)
        dv = (x2 - x0, y2 - y0)
        phi = lambda z: z[0] * dv[0] + z[1] * dv[1]
        f0 = min(phi(c) for c in V) if V else 0
        X = {z for z in B1 if phi(z) >= f0} | {(z[0] - dv[0], z[1] - dv[1]) for z in B2 if phi(z) - phi(dv) >= f0} | V
        if d2 == d0 and abs(dv[0]) == abs(dv[1]) and dv != (0, 0) and all(B2.get((z[0] + dv[0], z[1] + dv[1]), 0) == B1.get(z, 0) for z in X):
            return True, k
        B0, x0, y0, d0 = B2, x2, y2, d2
    return False, None
holes, overlaps, checked, bad = [], [], 0, []
for j in range(2, 23):
    for n in range(2 * j, 2 * j + 70):
        owners = [(i, s) for i, p in enumerate(pieces) for s in members(p, n, j)]
        if len(owners) == 0: holes.append((n, j)); continue
        if len(owners) > 1: overlaps.append((n, j, owners)); continue
        i, (xs, ys) = owners[0]; p = pieces[i]
        P = p["P"][0] + p["P"][1] * xs + p["P"][2] * ys
        ok, k = concrete_certificate(n, j, P); checked += 1
        law = 16 * (n + 2 * j + 1) - 20
        if not ok or (P != law and 2 * P != law): bad.append((n, j, P, law, ok))
print(f"puntos revisados: {checked}; huecos: {len(holes)}; traslapes: {len(overlaps)}; fallos: {len(bad)}")
print("huecos:", holes[:10]); print("traslapes:", overlaps[:5]); print("fallos:", bad[:10])
