"""Réplica en Python del verificador 'U' (para el teorema de herencia), antes de escribirlo en Lean.
La regla U tiene 3N estados y la letra de c es R si c mod N < n: su trayectoria es la de RⁿLᵐ, pero sus
estados son los conteos de visitas (no dan la vuelta). El verificador exige que todo color leído esté en
[0, N+n], es decir < K = N+n+1, y compara conteos exactos al cerrar."""
import json, sys
sys.path.insert(0, '../prueba')
from replica_lean import k, add, sub, mulN, nn, parse, Fail, leaves, MOV
from simbolico import fmtc

def intervalo(v, nf, Nf):
    """0: [0,n-1] R; 1: [n,N-1] L; 2: [N,N+n-1] R; 3: {N+n} L.  Devuelve (indice, der, cota superior)."""
    if nn(sub(sub(nf, k(1)), v)): return 0, True, sub(nf, k(1))
    if nn(sub(v, nf)) and nn(sub(sub(Nf, k(1)), v)): return 1, False, sub(Nf, k(1))
    if nn(sub(v, Nf)) and nn(sub(sub(add(Nf, nf), k(1)), v)): return 2, True, sub(add(Nf, nf), k(1))
    if v == add(Nf, nf): return 3, False, add(Nf, nf)
    raise Fail(f"clasifU {v}")

def verificaU(nf, jf, pre, per, d, f0):
    Nf = add(add(nf, mulN(2, jf)), k(1))
    def look(cfg, x): return cfg.get(x, k(0))
    def corre(segs, X, hist, V):
        cfg, pos, dr, time = X; cfg = dict(cfg)
        for sg in segs:
            if sg == "P":
                v = look(cfg, pos); _, der, _ = intervalo(v, nf, Nf)
                hist.append((pos, dr, v, der)); V.append(pos)
                cfg[pos] = add(v, k(1))
                dr = (dr + 1) % 4 if der else (dr + 3) % 4
                pos = (pos[0] + MOV[dr][0], pos[1] + MOV[dr][1]); time = add(time, k(1))
            elif sg == "M": hist = []
            else:
                r = sg[1]
                if not hist: raise Fail("acel sin historial")
                w0 = hist[0]
                if not (w0[0] == pos and w0[1] == dr and nn(r)): raise Fail("acel inicio")
                cnt = {}
                for w in hist: cnt[w[0]] = cnt.get(w[0], 0) + 1
                for (c, _, v, der) in hist:
                    _, _, ub = intervalo(v, nf, Nf)
                    if not nn(sub(sub(ub, v), mulN(cnt[c], r))): raise Fail("condAcelU")
                for (c, _, _, _) in hist: cfg[c] = add(look(cfg, c), r)
                time = add(time, mulN(len(hist), r)); V += [w[0] for w in hist]; hist = []
        return (cfg, pos, dr, time), hist, V
    X1, h1, _ = corre(parse(pre), ({}, (0, 0), 0, k(0)), [], [])
    X2, h2, V2 = corre(parse(per), X1, list(h1), [])
    phi = lambda x: x[0] * d[0] + x[1] * d[1]
    (c1, p1, d1, t1), (c2, p2, d2, t2) = X1, X2
    if p2 != (p1[0] + d[0], p1[1] + d[1]) or d2 != d1: raise Fail("cierre pos/dir")
    if phi(d) < 0 or not all(phi(x) >= f0 for x in V2): raise Fail("cierre semiplano")
    bad = [x for x in list(c1) + [(q[0] - d[0], q[1] - d[1]) for q in c2]
           if phi(x) >= f0 and look(c2, (x[0] + d[0], x[1] + d[1])) != look(c1, x)]
    if bad: raise Fail(f"cierre conteos en {len(bad)} celdas, p.ej. {bad[0]}: {look(c1,bad[0])} vs {look(c2,(bad[0][0]+d[0],bad[0][1]+d[1]))}")
    return t1, sub(t2, t1)

if __name__ == "__main__":
    data = json.load(open("../prueba/arbol_B.json"))
    for name, t in data.items():
        for lf in leaves(t):
            if lf["tipo"] != "hoja": continue
            nf, jf = tuple(lf["n"]), tuple(lf["j"]); c = lf["cert"]
            linea = (sub(nf, mulN(2, jf)) == k(0))
            try:
                T1, P = verificaU(nf, jf, c["pre"], c["per"], tuple(c["deriva"]), c["f0"])
                print(f"{name} OK    n={fmtc(nf):12s} j={fmtc(jf):10s} {'(línea)' if linea else ''}")
            except Fail as e:
                print(f"{name} FALLA n={fmtc(nf):12s} j={fmtc(jf):10s} {'(línea)' if linea else ''}: {e}")
