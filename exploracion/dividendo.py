"""Regla para fabricar un tablero que, tras k pasos, deja la cuadrícula en blanco.
F^-k = R ∘ F^k ∘ R, donde R(C,p,d) = (C, p - D[d], d+2): retroceder una casilla y girar 180°.
Además se verifica que el número del tablero blanco es el 'residuo' k-ésimo del número del
tablero fabricado: x(blanco) = frac(2^k · x(B_-k)), como en la división larga."""
from fractions import Fraction
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
def F(state, k, record=None):
    B, (x, y), d = set(state[0]), state[1], state[2]
    for _ in range(k):
        b = (x, y) in B
        if record is not None: record.append(int(b))
        if b: d = (d + 3) % 4; B.remove((x, y))
        else: d = (d + 1) % 4; B.add((x, y))
        x += D[d][0]; y += D[d][1]
    return (B, (x, y), d)
def R(state):
    B, (x, y), d = state
    return (set(B), (x - D[d][0], y - D[d][1]), (d + 2) % 4)
def dividendo(k):
    return R(F(R((set(), (0, 0), 0)), k))
def numero(state, extra=40000, P=104):
    """Fracción exacta de la lectura de colores (preperiodo + periodo 104)."""
    c = []; F(state, extra, c)
    pre = len(c) - 5 * P
    while pre > 0 and c[pre - 1] == c[pre - 1 + P]: pre -= 1
    A = int("".join(map(str, c[:pre])) or "0", 2); Rr = int("".join(map(str, c[pre:pre + P])), 2)
    return Fraction(A * (2**P - 1) + Rr, 2**pre * (2**P - 1)), pre
if __name__ == "__main__":
    blanco = (set(), (0, 0), 0)
    xb, Tb = numero(blanco)
    print(f"tablero blanco: preperiodo {Tb}")
    for k in (1, 10, 500, 9976, 9976 + 104 * 10, 9976 + 104 * 50):
        S = dividendo(k)
        fin = F(S, k)
        ok = (not fin[0]) and fin[1] == (0, 0) and fin[2] == 0
        xk, Tk = numero(S, extra=k + 40000)
        resid = (2**k * xk) % 1
        print(f"k={k:6d}: negras={len(S[0]):5d}  hormiga en {S[1]} mirando {'NESO'[S[2]]}  "
              f"→ blanco en k pasos: {ok}   x(blanco) = frac(2^k·x): {resid == xb}   preperiodo de x: {Tk}")
