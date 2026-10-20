"""¿Dónde vive el 'denominador'? Mismo tablero (blanco), distintos operadores (reglas).
Para cada regla de 2 a 9 colores (empezando en R, por simetría de espejo) se busca
autopista: desplazamiento constante y no nulo cada P pasos, sostenido en el tramo final."""
import ctypes, itertools, json
import numpy as np
lib = ctypes.CDLL("./librule.so")
lib.run_rule.restype = ctypes.c_long
MAXS = 3_000_000
PX = np.zeros(MAXS + 2, dtype=np.int32); PY = np.zeros(MAXS + 2, dtype=np.int32)
def trajectory(rule):
    turns = (ctypes.c_int * len(rule))(*[1 if c == "R" else -1 for c in rule])
    n = lib.run_rule(len(rule), turns, MAXS, PX.ctypes.data_as(ctypes.POINTER(ctypes.c_int32)),
                     PY.ctypes.data_as(ctypes.POINTER(ctypes.c_int32)))
    return PX[:n + 1].copy(), PY[:n + 1].copy()
def highway(px, py, Pmax=6000):
    N = len(px) - 1
    for P in range(1, Pmax + 1):
        Wn = max(30 * P, 20000)
        if N < Wn + P: break
        vx, vy = px[N] - px[N - P], py[N] - py[N - P]
        if vx == 0 and vy == 0: continue
        if px[N - 1] - px[N - 1 - P] != vx or py[N - 7] - py[N - 7 - P] != vy: continue
        a = slice(N - Wn, N + 1); b = slice(N - Wn - P, N - P + 1)
        if np.all(px[a] - px[b] == vx) and np.all(py[a] - py[b] == vy):
            dx, dy = px[N - Wn:N + 1] - px[N - Wn - P:N - P + 1], py[N - Wn:N + 1] - py[N - Wn - P:N - P + 1]
            ok = (dx == vx) & (dy == vy); t = N - Wn
            # retroceder hasta el inicio exacto
            while t - P >= 0 and px[t] - px[t - P] == vx and py[t] - py[t - P] == vy: t -= 1
            return P, (int(vx), int(vy)), int(t - P + 1)
    return None
