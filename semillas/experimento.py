"""Hipótesis: el tamaño de la semilla mínima de la autopista (en información) predice cuánto explora
la hormiga antes de encontrarla. Para cada regla caótica del catálogo:
  - semilla: patrón finito mínimo (reducción voraz) desde el que la hormiga corre la autopista de inmediato;
  - espera: casillas distintas visitadas antes de la autopista, desde 200 tableros 5x5 al azar."""
import json, math, random, sys, time
import azar as Z
rng = random.Random(12345)
cat = json.load(open("../exploracion/pendientes.json"))
def primitiva(w):
    n = len(w)
    return not any(n % p == 0 and w[:p] * (n // p) == w for p in range(1, n))
reglas = sorted([r for r, v in cat.items() if 1000 <= v["inicio"] <= 2_000_000 and v["P"] <= 2500 and primitiva(r)],
                key=lambda r: (len(r), r))
print(f"reglas caóticas seleccionadas: {len(reglas)}", flush=True)

def valida(rule, seed, d, P, v):
    r = Z.correr(rule, seed, (0, 0), d, maxsteps=200 * P + 40000)
    return r["T"] is not None and r["P"] == P and tuple(r["v"]) == tuple(v) and r["T"] <= 2 * P

def semilla(rule):
    r0 = Z.correr(rule)
    if r0["T"] is None: return None
    T0, P, v = r0["T"], r0["P"], r0["v"]
    for rad in (50, 100):
        s = Z.correr(rule, snap_t=T0 + 20 * P, snap_r=rad)
        cells, d = s["foto"], s["dir_foto"]
        if valida(rule, cells, d, P, v): break
    else:
        return dict(T0=T0, P=P, v=v, K0=r0["K"], k=None)
    mejor = None
    for rep in range(3):
        cur = list(cells); rng.shuffle(cur); i = 0
        while i < len(cur):
            prueba = cur[:i] + cur[i + 1:]
            if valida(rule, prueba, d, P, v): cur = prueba
            else: i += 1
        if mejor is None or len(cur) < len(mejor): mejor = cur
    xs = [c[0] for c in mejor] or [0]; ys = [c[1] for c in mejor] or [0]
    area = (max(xs) - min(xs) + 1) * (max(ys) - min(ys) + 1)
    return dict(T0=T0, P=P, v=v, K0=r0["K"], k=len(mejor), area=area, semilla=mejor, d=d)

def esperas(rule, nruns=200):
    N = len(rule); Ks, Ts, fallos = [], [], 0
    for _ in range(nruns):
        cells = []
        for x in range(-2, 3):
            for y in range(-2, 3):
                c = rng.randrange(N)
                if c: cells.append((x, y, c))
        r = Z.correr(rule, cells, maxsteps=4_000_000)
        if r["T"] is None: fallos += 1
        else: Ks.append(r["K"]); Ts.append(r["T"])
    return Ks, Ts, fallos

res = {}
t0 = time.time()
for i, rule in enumerate(reglas):
    s = semilla(rule)
    if s is None or s["k"] is None:
        print(f"[{i+1}/{len(reglas)}] {rule}: sin semilla válida", flush=True); continue
    Ks, Ts, fallos = esperas(rule)
    s.update(N=len(rule), Ks=Ks, Ts=Ts, fallos=fallos)
    res[rule] = s
    mk = sum(Ks) / len(Ks) if Ks else float("nan")
    print(f"[{i+1}/{len(reglas)}] {rule:13s} N={len(rule):2d} P={s['P']:5d} semilla={s['k']:4d} casillas (área {s['area']:5d})  "
          f"espera media={mk:9.0f} casillas  éxitos={len(Ks)}/{len(Ks)+fallos}  [{time.time()-t0:.0f}s]", flush=True)
    json.dump(res, open("resultados_semillas.json", "w"))
print("FIN", flush=True)
