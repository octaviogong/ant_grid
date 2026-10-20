"""Robustez de la espera sin memoria y de la ley semilla–espera.
Subconjunto estratificado de reglas caóticas; tres tipos de tablero inicial al azar:
  A: 5×5, cada casilla con color uniforme en 0..N−1 (la condición original)
  B: 9×9, cada casilla no nula con probabilidad 0.3
  C: 15×15, cada casilla no nula con probabilidad 0.1
Por regla y condición: 400 corridas; espera en casillas nuevas (K) y en pasos (T)."""
import json, math, random, time
import numpy as np
import azar as Z
rng = random.Random(777)
R = json.load(open("resultados_semillas.json"))
tab = {r["rule"]: r for r in json.load(open("tabla_semillas.json"))}
cand = []
for rule, r in tab.items():
    Ts = R[rule]["Ts"]
    if np.mean(Ts) <= 300_000: cand.append((math.log2(r["espera"]), rule))
cand.sort()
# estratificar por espera: 8 franjas, hasta 5 reglas por franja
lo, hi = cand[0][0], cand[-1][0]
bins = [[] for _ in range(8)]
for w, rule in cand:
    b = min(7, int((w - lo) / (hi - lo + 1e-9) * 8)); bins[b].append(rule)
sel = ["RL"]
for b in bins:
    rng.shuffle(b)
    for rule in b[:5]:
        if rule not in sel: sel.append(rule)
print(f"reglas elegidas: {len(sel)} (de {len(cand)} con espera media ≤ 300 000 pasos)", flush=True)
COND = {"A": (5, None), "B": (9, 0.3), "C": (15, 0.1)}
def tablero(N, lado, p):
    h = lado // 2; cells = []
    for x in range(-h, h + 1):
        for y in range(-h, h + 1):
            if p is None:
                c = rng.randrange(N)
            else:
                c = rng.randrange(1, N) if rng.random() < p else 0
            if c: cells.append((x, y, c))
    return cells
out = {}
t0 = time.time()
for i, rule in enumerate(sel):
    N = len(rule); out[rule] = {}
    for cname, (lado, p) in COND.items():
        Ks, Ts, f = [], [], 0
        for _ in range(400):
            r = Z.correr(rule, tablero(N, lado, p), maxsteps=6_000_000)
            if r["T"] is None: f += 1
            else: Ks.append(r["K"]); Ts.append(r["T"])
        out[rule][cname] = dict(Ks=Ks, Ts=Ts, fallos=f)
    msg = "  ".join(f"{c}: K̄={np.mean(out[rule][c]['Ks']):8.0f} cv={np.std(out[rule][c]['Ks'])/np.mean(out[rule][c]['Ks']):.2f}" for c in COND)
    print(f"[{i+1}/{len(sel)}] {rule:13s} {msg}  [{time.time()-t0:.0f}s]", flush=True)
    json.dump(out, open("robustez.json", "w"))
print("FIN", flush=True)
