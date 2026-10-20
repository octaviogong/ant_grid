"""Experimentos: ¿la hormiga 'lee' la aritmética de la entrada?

Para cada instancia se mide:
  T        pasos de caos hasta la autopista certificada (futuro)
  T_pasado lo mismo corriendo el tiempo hacia atrás
  dir      dirección de la autopista
  z        qué tan atípico es log10(T) frente a K sustitutos con las mismas casillas
           negras barajadas en las mismas ranuras (misma densidad y geometría, sin aritmética)
Si la hormiga leyera la estructura aritmética, z se alejaría de 0 de forma sistemática
y T (o z) se correlacionaría con el invariante (periodo, preperiodo, etc.).
"""
import csv, math, random, sys, time
from math import comb, factorial, gcd
import numpy as np
from scipy import stats
import antlib as A
import codif as E

K = 40
MAXS = 50_000_000
rng = random.Random(2026)
ROWS = []

def logT(r): return math.log10(r["T"] + 1)

def measure(fam, sub, label, enc, inv, k=K):
    cells, slots = enc
    r = A.run(cells, maxsteps=MAXS)
    rb = A.run(cells, maxsteps=MAXS, backward=True)
    sur, fails = [], 0
    if 0 < len(cells) < len(slots):
        for _ in range(k):
            rs = A.run(rng.sample(slots, len(cells)), maxsteps=MAXS)
            if rs["ok"]: sur.append(logT(rs))
            else: fails += 1
    z = None
    if r["ok"] and len(sur) >= 10 and np.std(sur) > 0:
        z = (logT(r) - np.mean(sur)) / np.std(sur, ddof=1)
    row = dict(familia=fam, sub=sub, etiqueta=label, negras=len(cells), ranuras=len(slots),
               densidad=round(len(cells) / max(1, len(slots)), 4), T=r["T"], autopista=r["ok"],
               dir=r["dir"], T_pasado=rb["T"], dir_pasado=rb["dir"], negras_en_T=r["black_at_T"],
               z=None if z is None else round(z, 3),
               sust_media=None if not sur else round(float(np.mean(sur)), 3),
               sust_fallos=fails, **inv)
    ROWS.append(row)
    return row

def summarize(rows, inv_key=None, title=""):
    T = [r["T"] for r in rows if r["autopista"]]
    zs = [r["z"] for r in rows if r["z"] is not None]
    out = {"titulo": title, "n": len(rows), "con_autopista": len(T),
           "T_min": min(T), "T_mediana": int(np.median(T)), "T_max": max(T)}
    if zs:
        out["z_media"] = round(float(np.mean(zs)), 3)
        out["p_wilcoxon_z"] = float(stats.wilcoxon(zs).pvalue) if len(zs) >= 10 else None
        out["frac_|z|>2"] = round(float(np.mean([abs(z) > 2 for z in zs])), 3)
    if inv_key:
        pairs = [(r[inv_key], r["T"]) for r in rows if r["autopista"] and r.get(inv_key) is not None]
        if len(pairs) >= 8:
            x, y = zip(*pairs)
            rho = stats.spearmanr(x, y)
            out[f"rho({inv_key},T)"] = round(float(rho.statistic), 3)
            out["p_rho"] = float(rho.pvalue)
        pz = [(r[inv_key], r["z"]) for r in rows if r["z"] is not None and r.get(inv_key) is not None]
        if len(pz) >= 8:
            x, y = zip(*pz)
            rz = stats.spearmanr(x, y)
            out[f"rho({inv_key},z)"] = round(float(rz.statistic), 3)
            out["p_rho_z"] = float(rz.pvalue)
    dirs = [r["dir"] for r in rows if r["autopista"]]
    out["direcciones"] = {d: dirs.count(d) for d in ("NE", "NO", "SE", "SO")}
    return out

SUMMARIES = []
def report(s):
    SUMMARIES.append(s)
    print("\n== " + s["titulo"]); [print(f"   {k}: {v}") for k, v in s.items() if k != "titulo"]
    sys.stdout.flush()

t0 = time.time()
# ===================== 1. DIVISIONES ENTRE PRIMOS =====================
P = [p for p in E.primes(700) if p > 2]
for p in P:
    pre, per2 = E.period(1, p, 2)
    per10 = E.mult_order(10, p) if p != 5 else None
    inv = dict(p=p, q=None, periodo2=per2, periodo10=per10, primitiva2=int(per2 == p - 1))
    measure("primos", "A cociente 1/p", f"1/{p}", E.enc_cociente(1, p), inv)
    measure("primos", "B residuos 1/p", f"1/{p}", E.enc_residuos(1, p), inv)
for sub in ("A cociente 1/p", "B residuos 1/p"):
    rows = [r for r in ROWS if r["sub"] == sub]
    report(summarize(rows, "periodo2", f"Primos · {sub} · invariante: periodo en base 2"))
    report(summarize(rows, "periodo10", f"Primos · {sub} · invariante: periodo en base 10"))

P25 = P[:25]
for i, p in enumerate(P25):
    for q in P25[i + 1:]:
        pre, per2 = E.period(p, q, 2)
        measure("primos", "C par (p,q)", f"{p}/{q}", E.enc_par(p, q),
                dict(p=p, q=q, periodo2=per2, periodo10=E.mult_order(10, q) if q != 5 else None,
                     primitiva2=int(per2 == q - 1)))
rows = [r for r in ROWS if r["sub"] == "C par (p,q)"]
report(summarize(rows, "periodo2", "Primos · C par de vectores (p,q) · invariante: periodo de p/q en base 2"))
print(f"[{time.time()-t0:.0f}s]")

# --- prueba de fracciones equivalentes: (p,q) vs (kp,kq) vs control con mismas longitudes
eq = {}
for k in (2, 3, 5):
    base, equiv, ctrl, same = [], [], [], 0
    for i, p in enumerate(P25):
        for q in P25[i + 1:]:
            r0 = A.run(E.enc_par(p, q)[0]); r1 = A.run(E.enc_par(k * p, k * q)[0])
            a = rng.randrange(1 << ((k * p).bit_length() - 1), 1 << (k * p).bit_length())
            b = rng.randrange(1 << ((k * q).bit_length() - 1), 1 << (k * q).bit_length())
            r2 = A.run(E.enc_par(a, b)[0])
            base.append(logT(r0)); equiv.append(logT(r1)); ctrl.append(logT(r2)); same += r0["T"] == r1["T"]
    eq[k] = dict(rho_equivalente=round(float(stats.spearmanr(base, equiv).statistic), 3),
                 p_equiv=float(stats.spearmanr(base, equiv).pvalue),
                 rho_control=round(float(stats.spearmanr(base, ctrl).statistic), 3),
                 p_ctrl=float(stats.spearmanr(base, ctrl).pvalue),
                 T_identico=same, pares=len(base))
    print(f"\n== Fracciones equivalentes k={k}: {eq[k]}")

# --- misma entrada, distinto punto de lectura
sens = {}
for p in (7, 97, 691):
    cells, slots = E.enc_cociente(1, p)
    Ts = [A.run(cells, start=(x, 0), d=d)["T"] for x in range(128) for d in range(4)]
    Ts = [t for t in Ts if t is not None]
    sens[p] = dict(corridas=len(Ts), T_min=min(Ts), T_mediana=int(np.median(Ts)), T_max=max(Ts),
                   distintos=len(set(Ts)))
    print(f"\n== Punto de lectura, cinta 1/{p}: {sens[p]}")
print(f"[{time.time()-t0:.0f}s]")

# ===================== 2. SERIES DE POTENCIAS =====================
for Q in range(3, 512, 2):           # todos los Q(x) de grado 1..8 con Q(0)=1, sobre F2
    per = E.seq_period(Q)
    measure("series", "racional 1/Q(x)", f"1/Q, Q={bin(Q)[2:]}", E.tape(E.series_inv(Q, 128)),
            dict(periodo2=per, grado=Q.bit_length() - 1, nivel="1 racional (periódica)"))
for name, f in E.AUTOMATICAS.items():
    for j in range(20):
        measure("series", "algebraica (automática)", f"{name} desde {13*j}", E.tape(f(128, 13 * j)),
                dict(nivel="2 algebraica (automática)", fuente=name))
IRR = {name: E.irrational_bits(name, 128 * 20) for name in E.IRRACIONALES}
for name, bits in IRR.items():
    for j in range(20):
        measure("series", "dígitos de irracional", f"{name} bits {128*j}-{128*j+127}",
                E.tape(bits[128 * j:128 * (j + 1)]), dict(nivel="3 irracional (no periódica)", fuente=name))
for j in range(120):
    measure("series", "control aleatorio", f"azar {j}", E.tape([rng.randrange(2) for _ in range(128)]),
            dict(nivel="4 azar (control)"))
rat = [r for r in ROWS if r["sub"] == "racional 1/Q(x)"]
report(summarize(rat, "periodo2", "Series racionales 1/Q(x) mod 2 · invariante: periodo"))
for sub in ("algebraica (automática)", "dígitos de irracional", "control aleatorio"):
    report(summarize([r for r in ROWS if r["sub"] == sub], None, f"Series · {sub}"))
groups = [[r["z"] for r in ROWS if r["familia"] == "series" and r.get("nivel", "").startswith(lv) and r["z"] is not None]
          for lv in "1234"]
kw_z = stats.kruskal(*groups)
groupsT = [[logT(r) for r in ROWS if r["familia"] == "series" and r.get("nivel", "").startswith(lv)] for lv in "1234"]
kw_T = stats.kruskal(*groupsT)
print(f"\n== Kruskal-Wallis entre niveles (periódica/automática/irracional/azar): z p={kw_z.pvalue:.3g}  log T p={kw_T.pvalue:.3g}")
print("   medianas de z por nivel:", [round(float(np.median(g)), 3) for g in groups])
print("   medianas de T por nivel:", [int(10 ** np.median(g)) for g in groupsT])
print(f"[{time.time()-t0:.0f}s]")

for b in range(3, 41):
    measure("series", "potencias b^n", f"{b}^n, n=0..15", E.enc_filas([b ** n for n in range(16)]), dict(base=b))
report(summarize([r for r in ROWS if r["sub"] == "potencias b^n"], "base", "Potencias b^n (16 filas) · invariante: b"))

# ===================== 3. FACTORIALES =====================
for N in range(2, 65):
    measure("factoriales", "Pascal mod 2", f"C(n,k), {N} filas", E.enc_pascal(N),
            dict(filas=N, potencia_de_2=int(N & (N - 1) == 0)))
pas = [r for r in ROWS if r["sub"] == "Pascal mod 2"]
report(summarize(pas, "filas", "Pascal mod 2 = n!/(k!(n-k)!) mod 2 · invariante: filas"))
pw = [r["T"] for r in pas if r["potencia_de_2"]]; npw = [r["T"] for r in pas if not r["potencia_de_2"]]
print("   filas = potencia de 2 (triángulo de Sierpinski completo):", list(zip([r["filas"] for r in pas if r["potencia_de_2"]], pw)))

for N in range(3, 41):
    measure("factoriales", "n! apilados", f"1!..{N}!", E.enc_filas([factorial(n) for n in range(1, N + 1)]), dict(filas=N))
report(summarize([r for r in ROWS if r["sub"] == "n! apilados"], "filas", "Factoriales n! apilados · invariante: N"))

def ord2_factorial_oddpart(n):
    from math import lcm
    L = 1
    for p in E.primes(n):
        if p == 2: continue
        e = sum(n // p ** i for i in range(1, 40) if p ** i <= n)
        o = E.mult_order(2, p); s = 0; x = 2 ** o - 1
        while x % p == 0: x //= p; s += 1
        L = lcm(L, o * p ** max(0, e - s))
    return L
for n in range(3, 46):
    per = ord2_factorial_oddpart(n)
    measure("factoriales", "1/n! (división)", f"1/{n}!", E.tape(E.factorial_mantissa_bits(n)),
            dict(n=n, log10_periodo2=round(math.log10(per), 3)))
report(summarize([r for r in ROWS if r["sub"] == "1/n! (división)"], "log10_periodo2", "División 1/n! · invariante: log10 del periodo en base 2"))

# ===================== GLOBAL =====================
ok = [r for r in ROWS if r["autopista"]]
okb = [r for r in ROWS if r["T_pasado"] is not None]
print(f"\n== GLOBAL: instancias={len(ROWS)}  con autopista futura={len(ok)}  con autopista pasada={len(okb)}")
both = [r for r in ROWS if r["autopista"] and r["T_pasado"] is not None]
rp = stats.spearmanr([r["T"] for r in both], [r["T_pasado"] for r in both])
print(f"   rho(T_futuro, T_pasado) = {rp.statistic:.3f}  p={rp.pvalue:.3g}")
zs = [r["z"] for r in ROWS if r["z"] is not None]
print(f"   z global: media={np.mean(zs):.3f}  frac |z|>2 = {np.mean([abs(z)>2 for z in zs]):.3f}  (esperado ≈0.05)")
dens = stats.spearmanr([r["densidad"] for r in ok], [r["T"] for r in ok])
print(f"   rho(densidad, T) = {dens.statistic:.3f}  p={dens.pvalue:.3g}")
print(f"   fallos de sustitutos sin autopista: {sum(r['sust_fallos'] for r in ROWS)}")
print(f"[{time.time()-t0:.0f}s]")

keys = []
for r in ROWS:
    for k in r:
        if k not in keys: keys.append(k)
with open("resultados.csv", "w", newline="", encoding="utf-8") as fh:
    w = csv.DictWriter(fh, fieldnames=keys); w.writeheader(); w.writerows(ROWS)
import json
with open("resumen.json", "w", encoding="utf-8") as fh:
    json.dump(dict(resumenes=SUMMARIES, equivalentes=eq, punto_de_lectura=sens,
                   kruskal=dict(p_z=kw_z.pvalue, p_T=kw_T.pvalue)), fh, ensure_ascii=False, indent=1, default=str)
