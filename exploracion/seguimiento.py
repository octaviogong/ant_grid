"""Seguimiento: someter a controles más estrictos las señales de experimentos.py.

1. Par (p,q): ¿es la aritmética o es que todo primo impar tiene el bit menos y el más
   significativo en 1 (casillas fijas pegadas a la hormiga)?  -> sustitutos con extremos fijos
   y pares de impares al azar de la misma longitud.
2. Pascal: ¿Sierpinski o simplemente los bordes C(n,0)=C(n,n)=1? -> sustitutos con bordes fijos.
3. Propiedades aritméticas puras (independientes del tamaño): ¿2 es raíz primitiva mod q?
4. T_futuro vs T_pasado controlando tamaño y densidad.
5. Dirección de la autopista: ¿la fija la aritmética o la geometría?
"""
import math, random, csv
import numpy as np
from scipy import stats
import antlib as A
import codif as E

rng = random.Random(7)
K = 60
lt = lambda T: math.log10(T + 1)

def z_constrained(cells, fixed_slots, free_slots, k=K):
    """z de log T frente a sustitutos que conservan las ranuras fijas y barajan el resto."""
    cells = set(cells)
    fixed_black = [s for s in fixed_slots if s in cells]
    nfree = sum(1 for s in free_slots if s in cells)
    real = A.run(list(cells))
    if nfree == 0 or nfree == len(free_slots): return None, real, []
    sur, dirs = [], []
    for _ in range(k):
        r = A.run(fixed_black + rng.sample(free_slots, nfree))
        sur.append(lt(r["T"])); dirs.append(r["dir"])
    return (lt(real["T"]) - np.mean(sur)) / np.std(sur, ddof=1), real, dirs

def pair_slots(a, b):
    xa = [(i + 1, 0) for i in range(a.bit_length())]
    yb = [(0, j + 1) for j in range(b.bit_length())]
    fixed = [xa[0], xa[-1], yb[0], yb[-1]]           # bit menos y más significativo de cada vector
    free = xa[1:-1] + yb[1:-1]
    return fixed, free

def strata_partial(x, y, strata):
    """Spearman dentro de cada estrato (combinado por Fisher-z ponderado)."""
    zs, ws = [], []
    for s in set(strata):
        idx = [i for i, t in enumerate(strata) if t == s]
        if len(idx) < 6: continue
        xs = [x[i] for i in idx]; ys = [y[i] for i in idx]
        if len(set(xs)) < 2: continue
        r = stats.spearmanr(xs, ys).statistic
        if np.isnan(r): continue
        zs.append(np.arctanh(np.clip(r, -0.999, 0.999))); ws.append(len(idx) - 3)
    zbar = np.average(zs, weights=ws); se = 1 / math.sqrt(sum(ws))
    return float(np.tanh(zbar)), float(2 * stats.norm.sf(abs(zbar / se)))

out = {}
P = [p for p in E.primes(700) if p > 2]
P25 = P[:25]

# ---------- 1. par (p,q) con sustitutos de extremos fijos ----------
zs, per, idx2, bl, T_real, dirs_real, dirs_sur = [], [], [], [], [], [], []
for i, p in enumerate(P25):
    for q in P25[i + 1:]:
        cells, _ = E.enc_par(p, q)
        fixed, free = pair_slots(p, q)
        z, r, d = z_constrained(cells, fixed, free)
        if z is None: continue
        o = E.period(p, q, 2)[1]
        zs.append(z); per.append(o); idx2.append(o / (q - 1)); bl.append(q.bit_length())
        T_real.append(r["T"]); dirs_real.append(r["dir"]); dirs_sur += d
out["par_z_extremos_fijos"] = dict(n=len(zs), z_media=round(float(np.mean(zs)), 3),
    p_wilcoxon=float(stats.wilcoxon(zs).pvalue), frac_abs_z_2=round(float(np.mean(np.abs(zs) > 2)), 3))
r = stats.spearmanr(per, zs)
out["par_rho_periodo_z"] = dict(rho=round(float(r.statistic), 3), p=float(r.pvalue))
out["par_rho_periodo_T_dentro_de_longitud_de_q"] = dict(zip(("rho", "p"), strata_partial(per, T_real, bl)))
r = stats.spearmanr(idx2, T_real)
out["par_rho_(periodo/(q-1))_T"] = dict(rho=round(float(r.statistic), 3), p=float(r.pvalue))

# pares de impares al azar con las mismas longitudes de bits (nulo aritmético)
null_T, null_per, null_bl = [], [], []
for i, p in enumerate(P25):
    for q in P25[i + 1:]:
        for _ in range(4):
            a = rng.randrange(1 << (p.bit_length() - 1), 1 << p.bit_length()) | 1
            b = rng.randrange(1 << (q.bit_length() - 1), 1 << q.bit_length()) | 1
            null_T.append(A.run(E.enc_par(a, b)[0])["T"])
            null_per.append(E.period(a, b, 2)[1]); null_bl.append(b.bit_length())
mw = stats.mannwhitneyu(T_real, null_T)
out["par_primos_vs_impares_al_azar"] = dict(T_mediana_primos=int(np.median(T_real)),
    T_mediana_impares=int(np.median(null_T)), p_mannwhitney=float(mw.pvalue))
r = stats.spearmanr(null_per, null_T)
out["impares_al_azar_rho_periodo_T"] = dict(rho=round(float(r.statistic), 3), p=float(r.pvalue), n=len(null_T))
out["impares_al_azar_rho_periodo_T_dentro_de_longitud"] = dict(zip(("rho", "p"), strata_partial(null_per, null_T, null_bl)))

# ---------- 2. Pascal con bordes fijos ----------
zs_p, rows_p = [], []
for N in range(2, 65):
    cells, slots = E.enc_pascal(N)
    fixed = [(k, -n) for n in range(N) for k in (0, n)]
    free = [(k, -n) for n in range(N) for k in range(1, n)]
    z, r, d = z_constrained(cells, fixed, free)
    if z is not None: zs_p.append(z); rows_p.append((N, r["T"], round(z, 2)))
out["pascal_z_bordes_fijos"] = dict(n=len(zs_p), z_media=round(float(np.mean(zs_p)), 3),
    p_wilcoxon=float(stats.wilcoxon(zs_p).pvalue), frac_abs_z_2=round(float(np.mean(np.abs(zs_p) > 2)), 3))

# ---------- 3. propiedad aritmética pura: ¿2 es raíz primitiva mod p? ----------
rows = list(csv.DictReader(open("resultados.csv", encoding="utf-8")))
for sub in ("A cociente 1/p", "B residuos 1/p"):
    rr = [r for r in rows if r["sub"] == sub]
    prim = [int(r["T"]) for r in rr if r["primitiva2"] == "1"]
    nonp = [int(r["T"]) for r in rr if r["primitiva2"] == "0"]
    mw = stats.mannwhitneyu(prim, nonp)
    out[f"raiz_primitiva_{sub}"] = dict(n_prim=len(prim), n_no=len(nonp), T_med_prim=int(np.median(prim)),
                                        T_med_no=int(np.median(nonp)), p=float(mw.pvalue))
    # periodo normalizado (independiente del tamaño de p)
    x = [int(r["periodo2"]) / (int(r["p"]) - 1) for r in rr]; y = [int(r["T"]) for r in rr]
    rs = stats.spearmanr(x, y)
    out[f"periodo_normalizado_{sub}"] = dict(rho=round(float(rs.statistic), 3), p=float(rs.pvalue))

# ---------- 4. futuro vs pasado, controlando tamaño y densidad ----------
Tf = np.array([lt(int(r["T"])) for r in rows]); Tp = np.array([lt(int(r["T_pasado"])) for r in rows])
X = np.column_stack([np.ones(len(rows)), [math.log10(int(r["ranuras"])) for r in rows],
                     [float(r["densidad"]) for r in rows], [float(r["densidad"]) ** 2 for r in rows]])
res = lambda y: y - X @ np.linalg.lstsq(X, y, rcond=None)[0]
rp = stats.spearmanr(res(Tf), res(Tp))
out["futuro_vs_pasado"] = dict(rho_cruda=round(float(stats.spearmanr(Tf, Tp).statistic), 3),
                               rho_controlando_tamano_densidad=round(float(rp.statistic), 3), p=float(rp.pvalue))
dsame = np.mean([r["dir"] == {"NE": "SO", "SO": "NE", "NO": "SE", "SE": "NO"}[r["dir_pasado"]] for r in rows])
out["futuro_vs_pasado"]["frac_direcciones_opuestas"] = round(float(dsame), 3)

# ---------- 5. dirección: real vs sustitutos (par p,q) ----------
cats = ("NE", "NO", "SE", "SO")
obs = [dirs_real.count(c) for c in cats]
exp = np.array([dirs_sur.count(c) for c in cats], float); exp = exp / exp.sum() * len(dirs_real)
out["direccion_par_real_vs_sustitutos"] = dict(real=dict(zip(cats, obs)),
    esperado=dict(zip(cats, np.round(exp, 1))), p_chi2=float(stats.chisquare(obs, exp).pvalue))

# ---------- 6. invariantes exactos del operador ----------
# paridad: cada paso cambia en ±1 el número de negras y alterna la paridad de x+y
cells = E.enc_par(13, 97)[0]
ok = True
B = set(cells); x = y = 0; d = 0; n0 = len(B)
for t in range(1, 200001):
    if (x, y) in B: d = (d + 3) % 4; B.remove((x, y))
    else: d = (d + 1) % 4; B.add((x, y))
    x += A.D[d][0]; y += A.D[d][1]
    if (len(B) - n0 - t) % 2 or (x + y - t) % 2: ok = False; break
out["invariante_paridad_200k_pasos"] = ok
# negras netas por periodo de autopista
r0 = A.run([], maxsteps=10_000_000)
B = set(); x = y = 0; d = 0; hist = []
for t in range(r0["T"] + 104 * 50 + 1):
    if (x, y) in B: d = (d + 3) % 4; B.remove((x, y))
    else: d = (d + 1) % 4; B.add((x, y))
    x += A.D[d][0]; y += A.D[d][1]; hist.append(len(B))
deltas = {hist[r0["T"] + 104 * (k + 1)] - hist[r0["T"] + 104 * k] for k in range(40)}
out["negras_netas_por_periodo_de_autopista"] = sorted(deltas)

for k, v in out.items(): print(f"{k}: {v}")
print("Pascal (filas, T, z con bordes fijos):", rows_p[:12], "...")
