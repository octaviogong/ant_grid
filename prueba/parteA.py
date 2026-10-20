"""Parte A: la semilla H(n,m) inicia una autopista de periodo 16(n+m) - 20, para toda una región.
H se leyó de las simulaciones concretas; aquí se toma como DEFINICIÓN (fórmulas en n y j, m = 2j+1)
y la prueba no depende de cómo se obtuvo."""
from simbolico import Region, Ant, Indeterminado, fmt, add, sub, const, ZERO
def H(R):
    n = R.n(); j = R.j() if hasattr(R, 'j') else (0, 0, 1)
    def f(a=0, cn=0, cj=0):  # a + cn·n + cj·j
        return add(add(const(a), (n[0] * cn, n[1] * cn, n[2] * cn)), (j[0] * cj, j[1] * cj, j[2] * cj))
    return {(-2, 4): f(cj=1), (-1, 4): f(cj=1), (0, 4): f(cj=1),
            (-2, 3): f(cj=1), (-1, 3): f(cn=1, cj=2),
            (-2, 2): f(-1, cj=2), (-1, 2): f(-1, cj=1), (0, 2): f(cn=1),
            (-2, 1): f(-1, cj=2), (-1, 1): f(-1, cn=1, cj=2), (0, 1): f(1, cn=1, cj=-1),
            (-1, 0): f(-1, cn=1), (0, 0): f(-2, cn=1, cj=-1),
            (-1, -1): f(-1, cj=1)}
def prove_from(R, B0, p0, d0, max_events=3000, window=400):
    """Busca dos eventos e1 < e2 con misma dirección, deriva diagonal y el certificado corregido:
    config(e2)[x + deriva] = config(e1)[x] para toda x del semiplano S (ver certificado.py)."""
    A = Ant(R); A.B = {c: v for c, v in B0.items() if v != ZERO}; A.p = p0; A.d = d0
    snaps = [(dict(A.B), A.p, A.d, A.time, set())]
    try:
        while A.events < max_events:
            acc = A.try_accelerate()
            if acc: touched = set(A._last_cycle_cells)
            else: A.step(); touched = {A.hist[-1][0]}
            for k in range(len(snaps) - 1, -1, -1):
                snaps[k][4].update(touched)          # casillas tocadas desde el evento k
            for k in range(len(snaps) - 1, max(-1, len(snaps) - 1 - window), -1):
                B1, p1, d1, t1, V = snaps[k]
                if d1 != A.d: continue
                dv = (A.p[0] - p1[0], A.p[1] - p1[1])
                if dv == (0, 0) or abs(dv[0]) != abs(dv[1]): continue
                phi = lambda x: x[0] * dv[0] + x[1] * dv[1]
                f0 = min(phi(c) for c in V)
                X = {x for x in B1 if phi(x) >= f0} | {(x[0] - dv[0], x[1] - dv[1]) for x in A.B if phi(x) - phi(dv) >= f0} | V
                if all(A.B.get((x[0] + dv[0], x[1] + dv[1]), ZERO) == B1.get(x, ZERO) for x in X):
                    return dict(ok=True, P=sub(A.time, t1), inicio=t1, deriva=dv, celdas=len(V), eventos=A.events)
            snaps.append((dict(A.B), A.p, A.d, A.time, set()))
            if len(snaps) > window + 5: snaps.pop(0)
    except Indeterminado as e:
        return dict(ok=False, motivo=str(e), eventos=A.events, f=getattr(e, 'f', None))
    return dict(ok=False, motivo="sin cierre")

if __name__ == "__main__":
    for c0, J0 in [(0, 2), (-1, 2), (0, 1), (1, 1), (2, 1)]:
        R = Region(c0, J0)
        r = prove_from(R, H(R), (0, 0), 2)
        nm = f"n = 2j{c0:+d} + u, u >= 0, j >= {J0}  (m = 2j+1 >= {2*J0+1})"
        if r["ok"]:
            ley = sub(scale16 := (16 * (R.n()[0] + 1 + 0), 16 * R.n()[1], 16 * (R.n()[2] + 2)), const(20))
            print(f"{nm}:  DEMOSTRADO  periodo = {fmt(r['P'])}  ley 16(n+m)-20 = {fmt(ley)}  coincide: {r['P'] == ley}  deriva {r['deriva']}  casillas {r['celdas']}")
        else:
            print(f"{nm}:  no cerró: {r}")
