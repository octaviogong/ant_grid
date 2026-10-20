"""Verificación independiente (Python puro) de la hormiga 3D: ¿vuelve el tablero a vacío?"""
SYM = {"R": (1, 1), "L": (1, -1), "U": (2, 1), "D": (2, -1), "W": (3, 1), "X": (3, -1)}
def vec(a, d):
    v = [0] * d; v[abs(a) - 1] = 1 if a > 0 else -1; return tuple(v)
def sim(rule, d, steps):
    n = len(rule); B = {}; p = (0,) * d; frame = list(range(1, d + 1)); hist = []
    for t in range(1, steps + 1):
        c = B.get(p, 0); ax, s = SYM[rule[c]]
        f, e = frame[0], frame[ax]; frame[0] = s * e; frame[ax] = -s * f
        nc = (c + 1) % n
        if nc: B[p] = nc
        else: B.pop(p, None)
        p = tuple(a + b for a, b in zip(p, vec(frame[0], d)))
        if not B and all(a == 0 for a in p) and frame == list(range(1, d + 1)): hist.append(t)
    return hist
for rule, d in [("DL", 3), ("DDL", 3)]:
    h = sim(rule, d, 2000)
    print(rule, f"{d}D: vuelve a (tablero vacío, origen, orientación inicial) en los pasos {h[:6]}")
