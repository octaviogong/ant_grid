import ctypes, os, random
_dir = os.path.dirname(os.path.abspath(__file__))
_so = os.path.join(_dir, "libazar.so")
if not os.path.exists(_so):  # compila el núcleo en C la primera vez
    import subprocess
    subprocess.run(["gcc", "-O3", "-shared", "-fPIC", "-o", _so, os.path.join(_dir, "azar.c")], check=True)
_lib = ctypes.CDLL(_so)
_I = ctypes.POINTER(ctypes.c_int)
_lib.correr.argtypes = [ctypes.c_int, _I, ctypes.c_int, _I, _I, _I, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                        ctypes.c_long, ctypes.c_long, ctypes.c_int, _I, _I, _I, ctypes.c_int, ctypes.POINTER(ctypes.c_long)]
SNAPCAP = 200000
_sx = (ctypes.c_int * SNAPCAP)(); _sy = (ctypes.c_int * SNAPCAP)(); _sc = (ctypes.c_int * SNAPCAP)()
def correr(rule, cells=(), pos=(0, 0), d=0, maxsteps=4_000_000, snap_t=-1, snap_r=50):
    N = len(rule); turns = (ctypes.c_int * N)(*[1 if c == "R" else 0 for c in rule])
    cells = list(cells); n0 = len(cells)
    xs = (ctypes.c_int * max(1, n0))(*[c[0] for c in cells]); ys = (ctypes.c_int * max(1, n0))(*[c[1] for c in cells])
    cs = (ctypes.c_int * max(1, n0))(*[c[2] for c in cells])
    out = (ctypes.c_long * 8)()
    rc = _lib.correr(N, turns, n0, xs, ys, cs, pos[0], pos[1], d, maxsteps, snap_t, snap_r, _sx, _sy, _sc, SNAPCAP, out)
    if rc: raise RuntimeError(rc)
    r = dict(T=out[0] if out[0] >= 0 else None, P=out[1], v=(out[2], out[3]), K=out[4], pasos=out[5])
    if snap_t >= 0:
        r["foto"] = [(_sx[i], _sy[i], _sc[i]) for i in range(out[6])]; r["dir_foto"] = out[7]
    return r
