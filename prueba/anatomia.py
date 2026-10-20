"""Anatomía de un periodo de la autopista de RⁿLᵐ: corridas largas de giros a la derecha
(vueltas alrededor de un bloque) frente al resto (trayectos entre bloques)."""
import itertools
from certificado import analyze
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
def trace(n, m):
    r = analyze(n, m); t1, P = r["inicio"], r["P"]
    N = n + m; B = {}; x = y = 0; d = 0; reads = []
    for t in range(t1 + P):
        c = B.get((x, y), 0)
        if t >= t1: reads.append(c)
        d = (d + 1) % 4 if c < n else (d + 3) % 4
        B[(x, y)] = (c + 1) % N
        x += D[d][0]; y += D[d][1]
    return P, reads
def runs(n, reads):
    turns = ["R" if c < n else "L" for c in reads]
    # rotar para empezar justo después de la corrida R más larga (corte canónico)
    out, i = [], 0
    for k, g in itertools.groupby(turns): out.append((k, len(list(g))))
    return out
rows = []
for m in (5, 7, 9, 11):
    j = (m - 1) // 2
    for n in range(3 * j + 1, 3 * j + 6):
        P, reads = trace(n, m)
        rr = runs(n, reads)
        longR = sorted([L for k, L in rr if k == "R" and L >= 4 * (n - 3 * j) and L >= 4], reverse=True)
        rest = P - sum(longR)
        nL = sum(L for k, L in rr if k == "L")
        rows.append((n, m, j, P, longR, rest, nL))
        print(f"n={n:2d} m={m:2d} j={j}  P={P:4d}  corridas R largas={longR}  resto={rest:4d}  giros L={nL}")
