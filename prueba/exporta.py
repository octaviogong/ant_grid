"""Exporta la demostración simbólica a Lean: certificados por pieza y árbol de cobertura.

El motor de Python solo BUSCA; Lean VERIFICA. Para cada hoja del árbol de casos se graba la lista de
segmentos (paso / marca / acel r) hasta el cierre, y para cada nodo interno la forma en que se partió.
"""
import json, sys, os
import simbolico as S
from simbolico import Cone, ZERO, sub, add, const, Indeterminado
import division_casos as DC
from division_casos import split_sign, split_mod, child, NoAfin, law
from parteA import H

# --- instrumentar el motor para grabar segmentos --------------------------------------------------
_orig_step = S.Ant.step
_orig_try = S.Ant.try_accelerate

def _step(self):
    if not hasattr(self, "segs"): self.segs, self.hidx = [], []
    _orig_step(self)
    self.segs.append("P"); self.hidx.append(len(self.segs) - 1)

def _try(self):
    if not hasattr(self, "segs"): self.segs, self.hidx = [], []
    key = (self.p, self.d)
    i0 = self.seen.get(key)
    hist_len = len(self.hist)
    ok = _orig_try(self)
    if ok:
        # el ciclo eran los pasos hist[i0:]; insertar una marca justo antes del paso i0
        pos = self.hidx[i0]
        self.segs.insert(pos, "M")
        self.segs.append(("A", self._last_r))
        self.hidx = []
    return ok

S.Ant.step = _step
S.Ant.try_accelerate = _try

# guardar r en la aceleración (parche mínimo sobre el original)
_src_scale = S.scale
def _accel_with_r(self):
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
        slack = sub(sub(self.n, const(1)), v) if k == "R" else sub(sub(self.N, const(2)), v)
        caps.append(S.floordiv(slack, delta[c], R))
    r = S.amin(caps, R)
    if r == ZERO or not R.nonneg(r): return False
    for c, dc in delta.items():
        self.B[c] = add(self.val(c), S.scale(r, dc))
    self.time = add(self.time, S.scale(r, len(cyc)))
    self.events += 1
    self._last_cycle_cells = set(delta)
    self._last_r = r
    self.hist = []; self.seen = {key: 0}
    return True
_orig_try = _accel_with_r

def prove_cert(R, B0, p0, d0, max_events=6000, window=600):
    A = S.Ant(R); A.B = {c: v for c, v in B0.items() if v != ZERO}; A.p = p0; A.d = d0
    A.segs, A.hidx = [], []
    snaps = [(dict(A.B), A.p, A.d, A.time, set(), 0)]
    try:
        while A.events < max_events:
            acc = A.try_accelerate()
            if acc: touched = set(A._last_cycle_cells)
            else: A.step(); touched = {A.hist[-1][0]}
            for k in range(len(snaps) - 1, -1, -1): snaps[k][4].update(touched)
            for k in range(len(snaps) - 1, max(-1, len(snaps) - 1 - window), -1):
                B1, p1, d1, t1, V, ev1 = snaps[k]
                if d1 != A.d: continue
                dv = (A.p[0] - p1[0], A.p[1] - p1[1])
                if dv == (0, 0) or abs(dv[0]) != abs(dv[1]): continue
                phi = lambda x: x[0] * dv[0] + x[1] * dv[1]
                f0 = min(phi(c) for c in V)
                X = {x for x in B1 if phi(x) >= f0} | {(x[0] - dv[0], x[1] - dv[1]) for x in A.B if phi(x) - phi(dv) >= f0} | V
                if all(A.B.get((x[0] + dv[0], x[1] + dv[1]), ZERO) == B1.get(x, ZERO) for x in X):
                    # cortar la lista de segmentos tras el evento ev1
                    cut, cnt = 0, 0
                    for idx, sg in enumerate(A.segs):
                        if cnt == ev1: cut = idx; break
                        if sg != "M": cnt += 1
                    else:
                        cut = len(A.segs)
                    if ev1 == 0: cut = 0
                    return dict(ok=True, P=sub(A.time, t1), inicio=t1, deriva=dv, f0=f0,
                                pre=A.segs[:cut], per=A.segs[cut:])
            snaps.append((dict(A.B), A.p, A.d, A.time, set(), A.events))
            if len(snaps) > window + 5: snaps.pop(0)
    except Indeterminado as e:
        return dict(ok=False, motivo=str(e), f=getattr(e, "f", None))
    return dict(ok=False, motivo="sin cierre")

def tree(R, seed, depth=0, maxdepth=16):
    B0, p0, d0 = seed(R)
    try:
        r = prove_cert(R, B0, p0, d0)
    except NoAfin as e:
        return dict(tipo="nodo", n=R.n(), j=R.j(), hijos=[tree(child(R, M, tag), seed, depth + 1) for M, tag in split_mod(R, e.f, e.k)])
    if r["ok"]:
        return dict(tipo="hoja", n=R.n(), j=R.j(), cert=r)
    if r.get("f") is not None and depth < maxdepth:
        return dict(tipo="nodo", n=R.n(), j=R.j(), hijos=[tree(child(R, M, tag), seed, depth + 1) for M, tag in split_sign(R, r["f"])])
    return dict(tipo="falla", n=R.n(), j=R.j(), motivo=r.get("motivo"))

def compress(segs):
    out = []; run = 0
    for sg in segs:
        if sg == "P": run += 1; continue
        if run: out.append(f"P{run}"); run = 0
        if sg == "M": out.append("M")
        else: out.append("A{},{},{}".format(*sg[1]))
    if run: out.append(f"P{run}")
    return " ".join(out)

def leaves(t):
    if t["tipo"] == "nodo":
        for h in t["hijos"]: yield from leaves(h)
    else: yield t

if __name__ == "__main__":
    blank = lambda R: ({}, (0, 0), 0)
    conos = {"m5": Cone((4, 1, 2), (2, 0, 1), "B"), "m3": Cone((3, 1, 0), (1, 0, 0), "B3"),
             "m1": Cone((2, 1, 0), (0, 0, 0), "B1")}
    pedidos = sys.argv[1:] or ["m5", "m3"]
    destino = "arbol_B.json"
    out = json.load(open(destino)) if os.path.exists(destino) else {}
    for name in pedidos:
        t = tree(conos[name], blank)
        for lf in leaves(t):
            if lf["tipo"] == "hoja":
                c = lf["cert"]; c["pre"] = compress(c["pre"]); c["per"] = compress(c["per"])
        out[name] = t
        ls = list(leaves(t))
        print(name, "hojas:", len(ls), "fallas:", [(l["n"], l["j"]) for l in ls if l["tipo"] == "falla"], flush=True)
    def enc(o):
        if isinstance(o, tuple): return list(o)
        raise TypeError
    json.dump(out, open(destino, "w"), default=enc)
