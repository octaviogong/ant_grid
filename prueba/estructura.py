"""Estructura de un periodo: secuencia de giros comprimida y estados leídos."""
from certificado import simulate, candidate, certify
import itertools
def period_trace(n, m):
    pos, dirs, _ = simulate(n, m, 60000)
    P, v, t_on = candidate(pos)
    t1 = certify(n, m, P, v, t_on)
    # re-simular registrando estados leídos
    N = n + m; B = {}; x = y = 0; d = 0; reads = []; turns = []
    D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
    for t in range(t1 + P):
        c = B.get((x, y), 0)
        if t >= t1: reads.append(c); turns.append("R" if c < n else "L")
        d = (d + 1) % 4 if c < n else (d + 3) % 4
        c2 = (c + 1) % N
        if c2: B[(x, y)] = c2
        else: B.pop((x, y), None)
        x += D[d][0]; y += D[d][1]
    return P, v, reads, turns
def rle(seq):
    return [(k, len(list(g))) for k, g in itertools.groupby(seq)]
for n, m in [(10, 5), (11, 5), (12, 5), (10, 7)]:
    P, v, reads, turns = period_trace(n, m)
    r = rle(turns)
    print(f"n={n} m={m} P={P} deriva={v}")
    print("   giros:", " ".join(f"{k}{c}" for k, c in r))
