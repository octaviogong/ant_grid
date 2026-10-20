"""Para un periodo de la autopista (régimen n >= 3j): bloques de cada giro, valores al empezar,
y los trayectos de conexión (longitud, giros, casillas que modifican)."""
import itertools, sys
from certificado import analyze
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
DN = "NESO"
def periodo(n, m):
    r = analyze(n, m); t1, P = r["inicio"], r["P"]
    N = n + m; B = {}; x = y = 0; d = 0; log = []
    for t in range(t1 + 2 * P):
        c = B.get((x, y), 0)
        if t >= t1: log.append(((x, y), d, c, "R" if c < n else "L"))
        d = (d + 1) % 4 if c < n else (d + 3) % 4
        B[(x, y)] = (c + 1) % N
        x += D[d][0]; y += D[d][1]
    return P, r["v"], log
def segmentos(log, P, minrun):
    # cortar el periodo en corridas R largas (giros) y lo demás (conexiones), empezando en un giro
    turns = [e[3] for e in log]
    runs, i = [], 0
    for k, g in itertools.groupby(range(len(turns)), key=lambda t: turns[t]):
        g = list(g); runs.append((k, g[0], len(g)))
    spins = [(s, L) for k, s, L in runs if k == "R" and L >= minrun and s < P]
    return spins
if __name__ == "__main__":
    n, m = int(sys.argv[1]), int(sys.argv[2]); j = (m - 1) // 2
    P, v, log = periodo(n, m)
    spins = segmentos(log, P, 4 * (n - 3 * j) if n > 3 * j else 4 * (n - j))
    print(f"n={n} m={m} j={j} N={n+m} P={P} deriva={v}")
    p0 = log[spins[0][0]][0]
    for idx, (s, L) in enumerate(spins):
        cells = [log[s + k][0] for k in range(4)]
        vals = [log[s + k][2] for k in range(4)]
        rel = [(c[0] - p0[0], c[1] - p0[1]) for c in cells]
        # siguiente giro (o el primero + P)
        s2 = spins[idx + 1][0] if idx + 1 < len(spins) else spins[0][0] + P
        con = log[s + L: s2]
        rle = " ".join(f"{k}{len(list(g))}" for k, g in itertools.groupby(e[3] for e in con))
        print(f" giro {idx+1}: {L:3d} pasos = 4·{L//4}+{L%4}; bloque {rel}; valores al empezar {vals}")
        print(f"    conexión {idx+1}: {len(con):3d} pasos, giros: {rle}")
        print(f"       lee: {[e[2] for e in con]}")
