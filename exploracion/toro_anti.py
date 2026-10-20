"""¿El número decodificado en un toro es 'antiperiódico'? (c[t+P/2] = 1 - c[t], es decir,
denominador que divide a 2^(P/2)+1, como 1/5 = 0.(0011) y 1/17 = 0.(00001111))."""
import numpy as np
D = [(0,1),(1,0),(0,-1),(-1,0)]
def seq(N, M):
    B = np.zeros((N, M), np.uint8); x = y = d = 0; c = []
    while True:
        b = B[y, x]; c.append(b)
        d = (d + 3) % 4 if b else (d + 1) % 4; B[y, x] ^= 1
        x = (x + D[d][0]) % M; y = (y + D[d][1]) % N
        if x == 0 and y == 0 and d == 0 and not B.any(): return np.array(c, np.uint8)
res = []
for N in range(1, 7):
    for M in range(N, 9):
        if N * M > 48: continue
        c = seq(N, M); P = len(c); h = P // 2
        anti = bool(np.all(c[h:] == 1 - c[:h]))
        # periodo mínimo de la sucesión de colores
        pmin = next(p for p in range(1, P + 1) if P % p == 0 and np.array_equal(np.roll(c, -p), c))
        res.append((N, M, P, pmin, anti))
        print(f"{N}x{M}: periodo de la órbita={P:7d}  periodo de los colores={pmin:7d}  antiperiódico={anti}")
print("antiperiódicos:", sum(r[4] for r in res), "de", len(res))
