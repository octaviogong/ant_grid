"""Hormiga en d dimensiones: envoltura, detección de autopista y canonización de reglas por simetría."""
import ctypes, itertools
import numpy as np
from math import gcd
lib = ctypes.CDLL("./libantnd.so"); lib.run_nd.restype = ctypes.c_long
SYM = {"R": (1, 1), "L": (1, -1), "U": (2, 1), "D": (2, -1), "W": (3, 1), "X": (3, -1)}
AXES = {2: "RL", 3: "RLUD", 4: "RLUDWX"}
_buf = {}
def run(rule, d, maxsteps, init=None):
    n = len(rule)
    ax = (ctypes.c_int * n)(*[SYM[c][0] for c in rule]); sg = (ctypes.c_int * n)(*[SYM[c][1] for c in rule])
    key = (d, maxsteps)
    if key not in _buf: _buf.clear(); _buf[key] = np.zeros((maxsteps + 1) * d, dtype=np.int32)
    tr = _buf[key]
    init = init or []
    xyz = (ctypes.c_int * max(1, len(init) * d))(*[v for cell, _ in init for v in cell])
    cc = (ctypes.c_int * max(1, len(init)))(*[c for _, c in init])
    N = lib.run_nd(d, n, ax, sg, maxsteps, len(init), xyz, cc, tr.ctypes.data_as(ctypes.POINTER(ctypes.c_int32)))
    if N < 0: raise RuntimeError(N)
    return tr[:(N + 1) * d].reshape(N + 1, d)
def highway(T, Pmax=8000):
    """Autopista: T[t]-T[t-P] constante y no nula en el tramo final.  Ciclo: constante y nula."""
    N = len(T) - 1
    for P in range(1, Pmax + 1):
        W = max(30 * P, 30000)
        if N < W + P: break
        v = T[N] - T[N - P]
        if not np.array_equal(T[N - 1] - T[N - 1 - P], v): continue
        if np.array_equal(T[N - W:N + 1] - T[N - W - P:N - P + 1], np.broadcast_to(v, (W + 1, T.shape[1]))):
            diff = T[P:] - T[:-P]; ok = np.all(diff == v, axis=1)
            bad = np.nonzero(~ok)[0]
            start = int(bad[-1] + 1) if len(bad) else 0
            return dict(P=P, v=tuple(int(a) for a in v), inicio=start, tipo="autopista" if np.any(v) else "ciclo")
    return None
def direction_class(v):
    a = sorted((abs(x) for x in v if x != 0), reverse=False)
    g = 0
    for x in a: g = gcd(g, x)
    return tuple(sorted((abs(x) // g for x in v), reverse=True))
def symmetries(d):
    """Simetrías del marco del cuerpo: permutaciones y cambios de signo de los ejes 1..d-1."""
    k = d - 1; out = []
    for perm in itertools.permutations(range(k)):
        for signs in itertools.product((1, -1), repeat=k):
            m = {}
            for i in range(k):
                for s in (1, -1):
                    src = next(c for c, (a, sg) in SYM.items() if a == i + 1 and sg == s)
                    dst = next(c for c, (a, sg) in SYM.items() if a == perm[i] + 1 and sg == s * signs[i])
                    m[src] = dst
            out.append(m)
    return out
def canonical_rules(d, n):
    syms = symmetries(d); seen = set(); reps = []
    for rule in itertools.product(AXES[d], repeat=n):
        r = "".join(rule)
        can = min("".join(m[c] for c in r) for m in syms)
        if can not in seen: seen.add(can); reps.append(can)
    return reps
def eff_dim(rule):
    return 1 + len({SYM[c][0] for c in rule})
