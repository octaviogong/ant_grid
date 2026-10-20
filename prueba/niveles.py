"""Historia de las casillas de cada bloque: cuántas veces las visita cada fase y con qué valor llegan."""
import sys
from bloques import periodo, segmentos
for n, m in [(13, 7), (17, 9), (21, 11)]:
    j = (m - 1) // 2
    P, v, log = periodo(n, m)
    spins = segmentos(log, P, 4 * (n - 3 * j))
    # fases: giro1, conexión1, giro2, conexión2, ...
    fases = []
    for i, (s, L) in enumerate(spins):
        s2 = spins[i + 1][0] if i + 1 < len(spins) else spins[0][0] + P
        fases.append((f"G{i+1}", s, s + L)); fases.append((f"C{i+1}", s + L, s2))
    print(f"n={n} m={m} j={j}")
    for b, (s, L) in enumerate(spins):
        cells = [log[s + k][0] for k in range(4)]
        for c in cells:
            hist = []
            for name, a, z in fases:
                k = sum(1 for e in log[a:z] if e[0] == c)
                if k: hist.append(f"{name}:+{k}")
            print(f"   bloque {b+1} casilla {c}: llega con {log[s + cells.index(c)][2]:2d}   visitas por fase en un periodo: {' '.join(hist)}")
    print()
