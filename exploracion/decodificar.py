"""Decodificar un tablero como fracción: el color que pisa la hormiga en el paso t es la
cifra binaria de 2^-t. x = 0.c1 c2 c3 ... (base 2). La conjetura de la autopista dice
exactamente que x es racional para todo tablero finito."""
from math import gcd
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
def colores(B0, n):
    B = set(B0); x = y = 0; d = 0; c = []
    for _ in range(n):
        black = (x, y) in B; c.append(1 if black else 0)
        if black: d = (d + 3) % 4; B.remove((x, y))
        else: d = (d + 1) % 4; B.add((x, y))
        x += D[d][0]; y += D[d][1]
    return c
def preperiodo_y_periodo(c, Pmax=500, cola=20000):
    n = len(c)
    for P in range(1, Pmax + 1):
        if all(c[i] == c[i - P] for i in range(n - cola, n)):
            t = n - cola
            while t - P >= 0 and c[t - 1] == c[t - 1 - P]: t -= 1
            return t - P, P   # preperiodo = primeras (t-P) cifras... ver abajo
    return None
def fraccion(c, pre, P):
    A = int("".join(map(str, c[:pre])) or "0", 2)
    R = int("".join(map(str, c[pre:pre + P])), 2)
    num = A * (2**P - 1) + R; den = 2**pre * (2**P - 1)
    g = gcd(num, den); return num // g, den // g
for nombre, B in [("blanco", set()), ("2 diag", {(0, 0), (1, 1)}), ("3 diag", {(0, 0), (1, 1), (2, 2)})]:
    c = colores(B, 60000)
    pre, P = preperiodo_y_periodo(c)
    # ajustar: buscar el preperiodo mínimo exacto
    while pre > 0 and all(c[i] == c[i + P] for i in range(pre - 1, len(c) - P)): pre -= 1
    while not all(c[i] == c[i + P] for i in range(pre, len(c) - P)): pre += 1
    num, den = fraccion(c, pre, P)
    v2 = (den & -den).bit_length() - 1; odd = den >> v2
    rep = "".join(map(str, c[pre:pre + P]))
    print(f"{nombre}: preperiodo={pre} cifras, periodo={P}, unos en el periodo={rep.count('1')}")
    print(f"   x = num/den, num con {len(str(num))} dígitos decimales, den = 2^{v2} · {odd}")
    print(f"   den impar == 2^{P}-1 ? {odd == 2**P - 1}   (2^{P}-1)/den_impar = {(2**P-1)//odd if (2**P-1)%odd==0 else 'no divide'}")
    print(f"   repetendo: {rep}")
    print(f"   primeras 40 cifras: 0.{''.join(map(str, c[:40]))}...")
    # rotación del repetendo respecto al del tablero blanco
    if nombre == "blanco": base_rep = rep
    else:
        rots = [k for k in range(P) if (base_rep[k:] + base_rep[:k]) == rep]
        print(f"   ¿mismo repetendo que el blanco salvo rotación? {bool(rots)} (rotación {rots[:1]})")
