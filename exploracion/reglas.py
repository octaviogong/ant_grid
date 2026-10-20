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
res = {}
for L in range(2, 10):
    for tail in itertools.product("LR", repeat=L - 1):
        rule = "R" + "".join(tail)
        if set(rule) == {"R"}: continue
        px, py = trajectory(rule)
        h = highway(px, py)
        res[rule] = dict(pasos=len(px) - 1, autopista=h is not None,
                         P=h[0] if h else None, v=h[1] if h else None, inicio=h[2] if h else None)
hw = {r: v for r, v in res.items() if v["autopista"]}
print(f"reglas probadas: {len(res)}   con autopista desde tablero blanco (<= {MAXS:,} pasos): {len(hw)}")
periods = sorted({v['P'] for v in hw.values()})
print("periodos distintos encontrados:", len(periods))
print("periodos:", periods)
for r, v in sorted(hw.items(), key=lambda kv: (len(kv[0]), kv[0])):
    print(f"  {r:10s} P={v['P']:5d}  desplazamiento={v['v']}  caos={v['inicio']}")
json.dump(res, open("reglas.json", "w"), indent=1)
