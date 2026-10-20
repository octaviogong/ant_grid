"""Réplica fiel en Python del verificador `verificaS` de Lean (mismas reglas, mismo orden),
para depurar certificados antes de compilarlos en Lean."""
import json
from simbolico import fmtc

def k(n): return (n, 0, 0)
def add(f, g): return (f[0] + g[0], f[1] + g[1], f[2] + g[2])
def sub(f, g): return (f[0] - g[0], f[1] - g[1], f[2] - g[2])
def mulN(q, f): return (q * f[0], q * f[1], q * f[2])
def nn(f): return f[0] >= 0 and f[1] >= 0 and f[2] >= 0
MOV = [(0, 1), (1, 0), (0, -1), (-1, 0)]

def parse(s):
    out = []
    for tok in s.split():
        if tok[0] == "P": out += ["P"] * int(tok[1:])
        elif tok == "M": out.append("M")
        else: out.append(("A", tuple(int(x) for x in tok[1:].split(","))))
    return out

class Fail(Exception): pass

def verificaS(nf, jf, ini, d0, pre, per, d, f0):
    Nf = add(add(nf, mulN(2, jf)), k(1))
    if not (nn(nf) and nn(jf) and all(nn(v) for _, v in ini)): raise Fail("cono")
    def look(cfg, x): return cfg.get(x, k(0))
    def corre(segs, X, hist, V):
        cfg, pos, dr, time = X
        cfg = dict(cfg)
        for sg in segs:
            if sg == "P":
                v = look(cfg, pos)
                if nn(sub(sub(nf, v), k(1))): der = True
                elif nn(sub(v, nf)): der = False
                else: raise Fail(f"clasif {v}")
                if add(v, k(1)) == Nf: nv = k(0)
                elif nn(sub(sub(Nf, v), k(2))): nv = add(v, k(1))
                else: raise Fail("nuevo")
                hist.append((pos, dr, v, der)); V.append(pos)
                cfg[pos] = nv
                dr = (dr + 1) % 4 if der else (dr + 3) % 4
                pos = (pos[0] + MOV[dr][0], pos[1] + MOV[dr][1])
                time = add(time, k(1))
            elif sg == "M":
                hist = []
            else:
                r = sg[1]
                if not hist: raise Fail("acel sin historial")
                w0 = hist[0]
                if not (w0[0] == pos and w0[1] == dr and nn(r)): raise Fail("acel inicio")
                cnt = {}
                for w in hist: cnt[w[0]] = cnt.get(w[0], 0) + 1
                for (c, _, v, der) in hist:
                    f = sub(sub(sub(nf, k(1)), v), mulN(cnt[c], r)) if der else sub(sub(sub(Nf, k(2)), v), mulN(cnt[c], r))
                    if not nn(f): raise Fail("condAcel")
                for (c, _, _, _) in hist:
                    cfg[c] = add(look(cfg, c), r)
                time = add(time, mulN(len(hist), r))
                V += [w[0] for w in hist]
                hist = []
        return (cfg, pos, dr, time), hist, V
    X1, h1, _ = corre(parse(pre), (dict(ini), (0, 0), d0, k(0)), [], [])
    X2, h2, V2 = corre(parse(per), X1, list(h1), [])
    phi = lambda x: x[0] * d[0] + x[1] * d[1]
    (c1, p1, d1, t1), (c2, p2, d2, t2) = X1, X2
    if p2 != (p1[0] + d[0], p1[1] + d[1]) or d2 != d1: raise Fail("cierre pos/dir")
    if phi(d) < 0 or not all(phi(x) >= f0 for x in V2): raise Fail("cierre semiplano")
    for x in list(c1) + [(q[0] - d[0], q[1] - d[1]) for q in c2]:
        if phi(x) >= f0 and look(c2, (x[0] + d[0], x[1] + d[1])) != look(c1, x): raise Fail(f"cierre celda {x}")
    return t1, sub(t2, t1)

def leaves(t):
    if t["tipo"] == "nodo":
        for h in t["hijos"]: yield from leaves(h)
    else: yield t

if __name__ == "__main__":
    data = json.load(open("arbol_B.json"))
    for name, t in data.items():
        for lf in leaves(t):
            if lf["tipo"] != "hoja": print(name, "falla", lf["n"], lf["j"]); continue
            c = lf["cert"]; nf, jf = tuple(lf["n"]), tuple(lf["j"])
            try:
                T1, P = verificaS(nf, jf, [], 0, c["pre"], c["per"], tuple(c["deriva"]), c["f0"])
                law = sub(mulN(16, add(add(nf, mulN(2, jf)), k(1))), k(20))
                tag = "ley" if P == law else ("mitad" if mulN(2, P) == law else "OTRO")
                print(f"{name} OK  n={fmtc(nf):12s} j={fmtc(jf):10s} P={fmtc(P):16s} {tag}  T1={fmtc(T1)}  segs={len(c['pre'].split())}+{len(c['per'].split())}")
            except Fail as e:
                print(f"{name} FALLA n={fmtc(nf)} j={fmtc(jf)}: {e}")
