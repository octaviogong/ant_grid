"""Envoltura Python del núcleo en C + utilidades."""
import ctypes, os, random
import numpy as np
_lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)), "libant.so"))
_lib.run_ant.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
                         ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long, ctypes.POINTER(ctypes.c_long)]
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
DIRNAME = {(2, 2): "NE", (2, -2): "SE", (-2, -2): "SO", (-2, 2): "NO"}

def run(cells, start=(0, 0), d=0, maxsteps=3_000_000, backward=False):
    """Corre la hormiga. backward=True corre el pasado (hormiga invertida)."""
    cells = list(cells)
    if backward:  # pasado de (C,p,d) = futuro de (C, p - D[d], d+2)
        start = (start[0] - D[d][0], start[1] - D[d][1]); d = (d + 2) % 4
    n = len(cells)
    xs = (ctypes.c_int * max(n, 1))(*[c[0] for c in cells])
    ys = (ctypes.c_int * max(n, 1))(*[c[1] for c in cells])
    out = (ctypes.c_long * 7)()
    rc = _lib.run_ant(n, xs, ys, start[0], start[1], d, maxsteps, out)
    if rc != 0: raise RuntimeError(rc)
    T = out[0]
    return dict(T=T if T >= 0 else None, ok=T >= 0, v=(out[1], out[2]),
                dir=DIRNAME.get((out[1], out[2]), "?") if T >= 0 else None,
                steps=out[3], black_at_T=out[4], chaos_w=out[5], chaos_h=out[6])

def shuffle_surrogate(cells, rng):
    """Mismo número de casillas negras, misma caja, posiciones al azar."""
    cells = list(cells)
    xs = [c[0] for c in cells]; ys = [c[1] for c in cells]
    box = [(x, y) for x in range(min(xs), max(xs) + 1) for y in range(min(ys), max(ys) + 1)]
    return rng.sample(box, len(cells))
