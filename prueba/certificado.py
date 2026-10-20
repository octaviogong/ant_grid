"""Certificado exacto de autopista para la regla RⁿLᵐ desde el tablero blanco.

Lema (corregido). Sean t1 < t2 = t1 + P, d = pos(t2) - pos(t1) != 0, misma dirección en t1 y t2,
V = casillas visitadas en [t1, t2), φ(x) = <x, d> y S = {x : φ(x) >= min_{c en V} φ(c)}.
Si config(t2)[x + d] = config(t1)[x] para TODA x en S (no solo en V), entonces la hormiga repite
el periodo para siempre, desplazándose d cada P pasos.
Demostración: (i) como V ⊂ S, en [t2, t2+P) la hormiga lee en c + d lo mismo que leyó en c en
[t1, t1+P), por inducción sobre los pasos; luego visita V + d y cambia esas casillas igual.
(ii) La condición se hereda: para x en S, x + d está en S, así que
config(t2+P)[x + 2d] = config(t2)[x + 2d] + Δ(x + d) = config(t1)[x + d] + Δ(x + d) = config(t2)[x + d],
donde Δ(z) es el cambio de la casilla z en el primer periodo. Es la misma condición para (t2, t2+P)
en el semiplano S + d ⊂ S. Se itera.
(La versión anterior solo pedía la igualdad en V; eso NO basta: la hormiga puede estar recorriendo
una estructura finita que ella misma construyó, y la "autopista" se termina al acabarse la estructura.)
Como la configuración es finita, basta comprobar las casillas de S donde alguna de las dos es != 0.
"""
import sys, json

D = [(0, 1), (1, 0), (0, -1), (-1, 0)]

def simulate(n, m, steps, snapshot_at=()):
    N = n + m; B = {}; x = y = 0; d = 0
    pos = [(0, 0)]; dirs = [0]; snaps = {}
    want = set(snapshot_at)
    for t in range(steps):
        if t in want: snaps[t] = (dict(B), (x, y), d)
        c = B.get((x, y), 0)
        d = (d + 1) % 4 if c < n else (d + 3) % 4
        c = (c + 1) % N
        if c: B[(x, y)] = c
        else: B.pop((x, y), None)
        x += D[d][0]; y += D[d][1]
        pos.append((x, y)); dirs.append(d)
    if steps in want: snaps[steps] = (dict(B), (x, y), d)
    return pos, dirs, snaps

def candidate(pos, Pmax=6000, reps=6):
    T = len(pos) - 1
    for P in range(1, Pmax + 1):
        if T < (reps + 1) * P: break
        v = (pos[T][0] - pos[T - P][0], pos[T][1] - pos[T - P][1])
        if v == (0, 0): continue
        if all((pos[t][0] - pos[t - P][0], pos[t][1] - pos[t - P][1]) == v for t in range(T - reps * P, T + 1)):
            t = T - reps * P
            while t - P >= 0 and (pos[t][0] - pos[t - P][0], pos[t][1] - pos[t - P][1]) == v: t -= 1
            return P, v, t - P + 1 if t - P + 1 >= 0 else 0
    return None

def certify(n, m, P, v, t_on, tries=40):
    for k in range(tries):
        t1 = t_on + k * P; t2 = t1 + P
        pos, dirs, snaps = simulate(n, m, t2, snapshot_at=(t1, t2))
        (B1, p1, d1), (B2, p2, d2) = snaps[t1], snaps[t2]
        if d1 != d2 or (p2[0] - p1[0], p2[1] - p1[1]) != v: continue
        V = set(pos[t1:t2])
        phi = lambda x: x[0] * v[0] + x[1] * v[1]
        f0 = min(phi(c) for c in V)
        X = {x for x in B1 if phi(x) >= f0} | {(x[0] - v[0], x[1] - v[1]) for x in B2 if phi(x) - phi(v) >= f0} | V
        if all(B2.get((x[0] + v[0], x[1] + v[1]), 0) == B1.get(x, 0) for x in X):
            return t1
    return None

def analyze(n, m, budget=400_000):
    steps = 4000
    while steps <= budget:
        pos, _, _ = simulate(n, m, steps)
        cand = candidate(pos)
        if cand:
            P, v, t_on = cand
            t1 = certify(n, m, P, v, t_on)
            if t1 is not None:
                return dict(n=n, m=m, P=P, v=v, inicio=t1, certificado=True)
        steps *= 2
    return dict(n=n, m=m, P=None, certificado=False)

if __name__ == "__main__":
    nmax, m0, m1, mstep = map(int, sys.argv[1:5])
    out = []
    for m in range(m0, m1 + 1, mstep):
        for n in range(1, nmax + 1):
            r = analyze(n, m); out.append(r)
            print(json.dumps(r), flush=True)
    json.dump(out, open(sys.argv[5], "w"))
