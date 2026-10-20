"""Ejecución simbólica de la hormiga RⁿLᵐ con n y m como variables.

Parámetros: m = 2j + 1 y n = 2j + c0 + u, con u >= 0 y j >= J0 enteros (o u fijo en 0 para una
franja). Cada estado de casilla es una forma afín a + b·u + c·j. En cada paso hay que decidir si el
estado es < n (gira a la derecha) o >= n (izquierda), y si el incremento llega a N = n + m (vuelve a 0).
Cada decisión se resuelve para TODA la región a la vez:
    a + b·u + c·j >= 0 en toda la región  <=>  b >= 0, c >= 0 y a + c·J0 >= 0.
Si alguna decisión dependiera del punto de la región, el programa se detiene: entonces la región no
tiene un único comportamiento y la prueba no aplica.

Aceleración: si la hormiga vuelve a la misma (posición, dirección), el tramo intermedio es un ciclo.
Repetirlo r veces es válido mientras cada visita del ciclo conserve su clase (R o L) y ninguna
vuelva a 0; eso da r = mín_k ⌊holgura_k / Δ_k⌋, también simbólico. Así una vuelta de 4n pasos cuesta
una sola operación y la ejecución es finita para todos los n y m a la vez.
"""
from fractions import Fraction

class Region:
    def __init__(self, c0, J0, u_fixed=None):
        self.c0, self.J0, self.u_fixed = c0, J0, u_fixed
    def aff(self, a=0, u=0, j=0):
        if self.u_fixed is not None: a += u * self.u_fixed; u = 0
        return (a, u, j)
    def n(self): return self.aff(self.c0, 1, 2)
    def N(self): return add(self.n(), (1, 0, 2))
    def nonneg(self, f):
        a, b, c = f
        if b >= 0 and c >= 0 and a + c * self.J0 >= 0: return True
        if b <= 0 and c <= 0 and a + c * self.J0 < 0: return False
        raise Indeterminado(f"signo de {fmt(f)} depende del punto de la región")
    def eq(self, f, g): return f == g
    def lt(self, f, g): return not self.nonneg(sub(f, g))      # f < g
    def le(self, f, g): return self.nonneg(sub(g, f))

class Indeterminado(Exception): pass

def add(f, g): return (f[0] + g[0], f[1] + g[1], f[2] + g[2])
def sub(f, g): return (f[0] - g[0], f[1] - g[1], f[2] - g[2])
def scale(f, k): return (f[0] * k, f[1] * k, f[2] * k)
def const(a): return (a, 0, 0)
def fmt(f):
    a, b, c = f; s = []
    if b: s.append(f"{b}u")
    if c: s.append(f"{c}j")
    if a or not s: s.append(str(a))
    return "+".join(s).replace("+-", "-")
def floordiv(f, k, R):
    a, b, c = f
    if b % k or c % k: raise Indeterminado(f"⌊{fmt(f)}/{k}⌋ no es afín")
    return (a // k, b // k, c // k)
def amin(fs, R):
    best = fs[0]
    for g in fs[1:]:
        if R.lt(g, best): best = g
        elif not R.le(best, g): raise Indeterminado("mínimo indeterminado")
    return best

D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
ZERO = (0, 0, 0)

class Ant:
    def __init__(self, R):
        self.R = R; self.B = {}; self.p = (0, 0); self.d = 0; self.time = ZERO
        self.hist = []; self.seen = {}; self.events = 0; self.visited_since = set()
        self.n = R.n(); self.N = R.N()
    def val(self, c): return self.B.get(c, ZERO)
    def cls(self, v):  # 'R' si v < n, 'L' si n <= v
        return "R" if self.R.lt(v, self.n) else "L"
    def step(self):
        R = self.R; c = self.p; v = self.val(c); k = self.cls(v)
        self.hist.append((c, self.d, v, k))
        self.d = (self.d + 1) % 4 if k == "R" else (self.d + 3) % 4
        nv = add(v, const(1))
        if nv == self.N: nv = ZERO
        elif not R.lt(nv, self.N): raise Indeterminado(f"¿{fmt(nv)} llega a N?")
        if nv == ZERO: self.B.pop(c, None)
        else: self.B[c] = nv
        self.visited_since.add(c)
        self.p = (c[0] + D[self.d][0], c[1] + D[self.d][1])
        self.time = add(self.time, const(1)); self.events += 1
    def try_accelerate(self):
        key = (self.p, self.d)
        i0 = self.seen.get(key)
        self.seen[key] = len(self.hist)
        if i0 is None: return False
        cyc = self.hist[i0:]
        if not cyc: return False
        delta = {}
        for (c, d, v, k) in cyc: delta[c] = delta.get(c, 0) + 1
        R = self.R; caps = []
        for (c, d, v, k) in cyc:
            # en la repetición i (i = 1..r) esta visita lee v + i·Δ_c
            slack = sub(sub(self.n, const(1)), v) if k == "R" else sub(sub(self.N, const(2)), v)
            caps.append(floordiv(slack, delta[c], R))
        r = amin(caps, R)
        if r == ZERO or not R.nonneg(r): return False           # r >= 0 en toda la región (r = 0 es válido)
        for c, dc in delta.items():
            nv = add(self.val(c), scale(r, dc))
            self.B[c] = nv
        self.time = add(self.time, scale(r, len(cyc)))
        self.events += 1
        self._last_cycle_cells = set(delta)
        self.hist = []; self.seen = {key: 0}
        return True
    def advance(self):
        """Un evento: o una aceleración o un paso."""
        if not self.try_accelerate(): self.step()
    def snapshot(self):
        return (dict(self.B), self.p, self.d, self.time)

class Cone:
    """Región general: variables enteras s, t >= 0; n y j son formas afines (a, b_s, b_t)."""
    def __init__(self, n_form, j_form, nombre=""):
        self._n, self._j, self.nombre = n_form, j_form, nombre
    def n(self): return self._n
    def j(self): return self._j
    def N(self): return add(add(self._n, scale(self._j, 2)), const(1))
    def nonneg(self, f):
        a, b, c = f
        if b >= 0 and c >= 0 and a >= 0: return True
        if b <= 0 and c <= 0 and a < 0: return False
        raise Indeterminado(f"signo de {fmtc(f)} depende del punto de la región")
    def lt(self, f, g): return not self.nonneg(sub(f, g))
    def le(self, f, g): return self.nonneg(sub(g, f))
def fmtc(f):
    a, b, c = f; s = []
    if b: s.append(f"{b}s")
    if c: s.append(f"{c}t")
    if a or not s: s.append(str(a))
    return "+".join(s).replace("+-", "-")
