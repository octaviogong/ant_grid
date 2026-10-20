"""División automática de casos para la Parte A.

Una región es un cono {(x, y) enteros >= 0} con una sustitución afín (s, t) = M(x, y) hacia las
variables originales; n y j se recalculan en las nuevas variables. Si una decisión f = a + b·x + c·y
no tiene signo fijo, la región se parte en piezas que la cubren exactamente y en cada una f tiene
signo fijo (umbrales, franjas finitas y, cuando b y c tienen signos opuestos, residuos módulo b o c).
"""
import math, sys
import simbolico as S
from simbolico import Cone, fmtc, sub, const, add, scale
from parteA import H, prove_from

class NoAfin(Exception):
    def __init__(self, f, k): super().__init__(f"no afin {f} / {k}"); self.f, self.k = f, k

# instrumentar: que las excepciones lleven la forma
def _nonneg(self, f):
    a, b, c = f
    if b >= 0 and c >= 0 and a >= 0: return True
    if b <= 0 and c <= 0 and a < 0: return False
    e = S.Indeterminado(f"signo de {fmtc(f)}"); e.f = f; raise e
Cone.nonneg = _nonneg
def _floordiv(f, k, R):
    a, b, c = f
    if b % k or c % k: raise NoAfin(f, k)
    return (a // k, b // k, c // k)
S.floordiv = _floordiv

def subst(form, M):
    """form (a, b, c) en (x_old, y_old); M = ((a0, a1, a2), (b0, b1, b2)) da x_old, y_old en (x, y)."""
    a, b, c = form; (p0, p1, p2), (q0, q1, q2) = M
    return (a + b * p0 + c * q0, b * p1 + c * q1, b * p2 + c * q2)

def child(R, M, tag):
    return Cone(subst(R.n(), M), subst(R.j(), M), R.nombre + " | " + tag)

ID = ((0, 1, 0), (0, 0, 1))

def split_sign(R, f):
    a, b, c = f
    pieces = []
    if b == 0 and c == 0: raise RuntimeError("constante indeterminada")
    if (b >= 0 and c >= 0) or (b <= 0 and c <= 0):
        if b != 0: var, coef = 0, b
        else: var, coef = 1, c
        if coef > 0: th = math.ceil(-a / coef)          # f >= 0 desde var >= th
        else: th = a // (-coef) + 1                      # f < 0 desde var >= th
        th = max(th, 0)
        for k in range(th):
            M = ((k, 0, 0), (0, 0, 1)) if var == 0 else ((0, 1, 0), (k, 0, 0))
            # en la franja la variable fijada queda "muerta": su coeficiente es 0
            pieces.append((M, f"{'xy'[var]}={k}"))
        M = ((th, 1, 0), (0, 0, 1)) if var == 0 else ((0, 1, 0), (th, 0, 1))
        pieces.append((M, f"{'xy'[var]}>={th}"))
        return pieces
    # signos opuestos: hacemos que b > 0 > c (si no, intercambiamos x <-> y)
    swap = b < 0
    if swap: a, b, c = a, c, b
    C = -c
    # t = b·q + r ; f >= 0  <=>  s >= C·q + K_r,  K_r = ceil((C·r - a)/b)
    for r in range(b):
        K = math.ceil((C * r - a) / b)
        # parte f >= 0
        if K >= 0:
            pieces.append((((K, C, 1), (r, b, 0)), f"f>=0 r={r}"))        # s = K + C q + w, t = r + b q ; vars (q, w)
        else:
            qs = math.ceil(-K / C)
            for q in range(qs):
                pieces.append((((0, 0, 1), (r + b * q, 0, 0)), f"f>=0 r={r} q={q}"))   # s libre
            pieces.append((((K + C * qs, C, 1), (r + b * qs, b, 0)), f"f>=0 r={r} q>={qs}"))
        # parte f < 0: 0 <= s <= C q + K - 1 ; s = C·p + e  ->  q >= p + L_e, L_e = ceil((e - K + 1)/C)
        for e in range(C):
            L = math.ceil((e - K + 1) / C)
            if L >= 0:
                pieces.append((((e, C, 0), (r + b * L, b, b)), f"f<0 r={r} e={e}"))   # s = e + C p, q = p + L + w
            else:
                ps = -L
                for p in range(ps):
                    pieces.append((((e + C * p, 0, 0), (r, 0, b)), f"f<0 r={r} e={e} p={p}"))  # q libre
                pieces.append((((e + C * ps, C, 0), (r, b, b)), f"f<0 r={r} e={e} p>={ps}"))
    if swap:
        pieces = [(((M[1][0], M[1][1], M[1][2]), (M[0][0], M[0][1], M[0][2])), t) for M, t in pieces]
    return pieces

def split_mod(R, f, k):
    a, b, c = f; pieces = []
    rx = range(k) if b % k else [None]
    ry = range(k) if c % k else [None]
    for r1 in rx:
        for r2 in ry:
            px = (0, 1, 0) if r1 is None else (r1, k, 0)
            py = (0, 0, 1) if r2 is None else (r2, 0, k)
            pieces.append(((px, py), f"mod{k} {r1},{r2}"))
    return pieces

def law(R):
    return sub(scale(add(add(R.n(), scale(R.j(), 2)), const(1)), 16), const(20))

def prove_region(R, depth=0, maxdepth=16, out=None, budget=None, seed=None):
    budget = budget if budget is not None else [4000]
    seed = seed or (lambda R: (H(R), (0, 0), 2))
    out = out if out is not None else []
    budget[0] -= 1
    if budget[0] < 0: out.append((R, "presupuesto", None)); return out
    try:
        B0, p0, d0 = seed(R)
        r = prove_from(R, B0, p0, d0, max_events=6000, window=600)
    except NoAfin as e:
        if depth >= maxdepth: out.append((R, "profundidad", None)); return out
        for M, tag in split_mod(R, e.f, e.k): prove_region(child(R, M, tag), depth + 1, maxdepth, out, budget, seed)
        return out
    if r["ok"]:
        out.append((R, "ok" if r["P"] == law(R) else "PERIODO DISTINTO", r)); return out
    if r.get("f") is not None and depth < maxdepth:
        for M, tag in split_sign(R, r["f"]): prove_region(child(R, M, tag), depth + 1, maxdepth, out, budget, seed)
        return out
    out.append((R, "falla", r)); return out
