"""Codificaciones de 'pares de entrada' en la cuadrícula.

Cada codificador devuelve (celdas_negras, ranuras): las ranuras son las casillas que la
codificación puede usar; los sustitutos aleatorios barajan las casillas negras dentro de
esas mismas ranuras, así conservan número de negras y geometría pero pierden la aritmética.
La hormiga siempre empieza en (0,0) mirando al norte.
"""
from math import isqrt, comb, factorial

# ---------- aritmética ----------
def odd_part(n, base=2):
    for f in ((2,) if base == 2 else (2, 5)):
        while n % f == 0: n //= f
    return n

def mult_order(b, m):
    if m == 1: return 0
    k, x = 1, b % m
    while x != 1:
        x = x * b % m; k += 1
    return k

def period(a, q, base=2):
    """(preperiodo, periodo) de la expansión de a/q en la base dada."""
    from math import gcd
    g = gcd(a, q); q //= g
    pre, m = 0, q
    fs = (2,) if base == 2 else (2, 5)
    for f in fs:
        c = 0
        while m % f == 0: m //= f; c += 1
        pre = max(pre, c)
    return pre, mult_order(base, m)

def frac_bits(a, q, L):
    """Primeros L bits de la parte fraccionaria de a/q (división larga en base 2)."""
    r = a % q; out = []
    for _ in range(L):
        r *= 2; out.append(r // q); r %= q
    return out

def remainders(a, q, L):
    r = a % q; out = []
    for _ in range(L):
        out.append(r); r = 2 * r % q
    return out

def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\0\0"
    for i in range(2, isqrt(n) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

# ---------- codificaciones ----------
def tape(bits):
    """Cinta: bit i en (i, 0)."""
    slots = [(i, 0) for i in range(len(bits))]
    return [s for s, b in zip(slots, bits) if b], slots

def enc_cociente(a, q, L=128):
    """A: los primeros L bits del cociente a/q en una fila."""
    return tape(frac_bits(a, q, L))

def enc_residuos(a, q, L=64):
    """B: la tabla de la división larga; columna k = residuo r_k en binario (vertical)."""
    nb = max(1, q.bit_length())
    cells, slots = [], []
    for k, r in enumerate(remainders(a, q, L)):
        for j in range(nb):
            slots.append((k, j))
            if (r >> j) & 1: cells.append((k, j))
    return cells, slots

def enc_par(a, b):
    """C: par de vectores; a en binario sobre +x (x>=1), b sobre +y (y>=1), bit menos significativo junto al origen."""
    cells, slots = [], []
    for i in range(a.bit_length()):
        slots.append((i + 1, 0))
        if (a >> i) & 1: cells.append((i + 1, 0))
    for j in range(b.bit_length()):
        slots.append((0, j + 1))
        if (b >> j) & 1: cells.append((0, j + 1))
    return cells, slots

def enc_filas(nums, width=None):
    """Una fila por número (fila n en y=-n), bit menos significativo en x=0."""
    width = width or max(1, max(n.bit_length() for n in nums))
    cells, slots = [], []
    for r, n in enumerate(nums):
        for i in range(width):
            slots.append((i, -r))
            if (n >> i) & 1: cells.append((i, -r))
    return cells, slots

def enc_pascal(N):
    """Triángulo de Pascal mod 2: C(n,k) = n!/(k!(n-k)!) mod 2 en (k, -n)."""
    cells, slots = [], []
    for n in range(N):
        for k in range(n + 1):
            slots.append((k, -n))
            if (n & k) == k: cells.append((k, -n))   # Lucas: C(n,k) impar <=> k ⊆ n
    return cells, slots

# ---------- series de potencias sobre F2 ----------
def series_inv(Q, L):
    """Coeficientes mod 2 de 1/Q(x), Q dado como entero (bit i = coef de x^i), Q(0)=1."""
    q = [(Q >> i) & 1 for i in range(Q.bit_length())]
    c = []
    for n in range(L):
        s = 1 if n == 0 else 0
        for i in range(1, len(q)):
            if q[i] and n - i >= 0: s ^= c[n - i]
        c.append(s)
    return c

def seq_period(Q):
    """Periodo de 1/Q(x) mod 2 = orden de x en F2[x]/(Q) (si Q(0)=1)."""
    d = Q.bit_length() - 1
    if d == 0: return 1
    # potencia de x módulo Q hasta volver a 1
    def mulx(p):
        p <<= 1
        if (p >> d) & 1: p ^= Q
        return p
    p, k = mulx(1), 1
    while p != 1:
        p = mulx(p); k += 1
        if k > 1 << (d + 2): return None
    return k

def thue_morse(L, s=0): return [bin(n).count("1") % 2 for n in range(s, s + L)]
def rudin_shapiro(L, s=0): return [bin(n & (n >> 1)).count("1") % 2 for n in range(s, s + L)]
def paperfolding(L, s=0):
    out = []
    for n in range(s + 1, s + L + 1):
        m = n
        while m % 2 == 0: m //= 2
        out.append(1 if m % 4 == 1 else 0)
    return out
def period_doubling(L, s=0):
    out = []
    for n in range(s + 1, s + L + 1):
        v = (n & -n).bit_length() - 1
        out.append(v % 2)
    return out
def catalan_mod2(L, s=0): return [1 if ((n + 2) & (n + 1)) == 0 else 0 for n in range(s, s + L)]
def baum_sweet(L, s=0):
    out = []
    for n in range(s, s + L):
        ok = 1
        for blk in bin(n)[2:].split("1"):
            if len(blk) % 2 == 1 and n > 0: ok = 0; break
        out.append(ok if n > 0 else 1)
    return out
def powers_of_two_char(L, s=0): return [1 if n > 0 and (n & (n - 1)) == 0 else 0 for n in range(s, s + L)]

AUTOMATICAS = {"Thue-Morse": thue_morse, "Rudin-Shapiro": rudin_shapiro, "Plegado de papel": paperfolding,
               "Duplicación de periodo": period_doubling, "Catalan mod 2": catalan_mod2,
               "Baum-Sweet": baum_sweet, "Potencias de 2": powers_of_two_char}

# ---------- dígitos binarios de irracionales (aritmética entera exacta) ----------
def _arctan_inv(x, one):
    s, t, n, sign = 0, one // x, 1, 1
    x2 = x * x
    while t:
        s += sign * (t // n); t //= x2; n += 2; sign = -sign
    return s

def irrational_bits(name, L, guard=64):
    one = 1 << (L + guard)
    if name == "π":   v = 4 * (4 * _arctan_inv(5, one) - _arctan_inv(239, one))
    elif name == "e":
        v, t, k = 0, one, 0
        while t: v += t; k += 1; t //= k
    elif name == "√2": v = isqrt(2 * one * one)
    elif name == "√3": v = isqrt(3 * one * one)
    elif name == "φ":  v = (one + isqrt(5 * one * one)) // 2
    elif name == "ln 2":
        v, k = 0, 1
        while (one >> k) // k: v += (one >> k) // k; k += 1
    else: raise ValueError(name)
    frac = v % one
    bits = [(frac >> (L + guard - 1 - i)) & 1 for i in range(L)]
    return bits

IRRACIONALES = ["π", "e", "√2", "√3", "φ", "ln 2"]

def factorial_mantissa_bits(n, L=128):
    """Bits significativos de 1/n! (a partir del primer 1): división entre un factorial."""
    f = factorial(n)
    k = f.bit_length()            # 2^(k-1) <= n! < 2^k
    a = 1 << (k - 1)              # a/n! en [1/2, 1) → empieza con 1
    return frac_bits(a, f, L)
