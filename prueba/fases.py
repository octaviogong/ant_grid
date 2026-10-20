"""Reproduce el certificado del periodo de la pieza n = 3s + t + 7, j = s + 2 (régimen n ≥ 3j + 1) con la
misma semántica que el verificador de Lean, y describe cada fase en términos de n y j."""
import json
from replica_lean import parse, add, sub, mulN, nn, k, MOV
d = json.load(open("arbol_B.json"))
def leaves(t):
    if t["tipo"] == "nodo":
        for h in t["hijos"]: yield from leaves(h)
    else: yield t
import sys
PIEZAS = {"alto": ([7, 3, 1], [2, 1, 0], ((-2, 0, 1), (-1, 1, -3))),     # s = j − 2, t = n − 3j − 1
          "bajo": ([8, 5, 3], [3, 2, 1], ((-1, -1, 3), (-1, 2, -5)))}    # s = 3j − 1 − n, t = 2n − 5j − 1
cual = sys.argv[1] if len(sys.argv) > 1 else "alto"
nL, jL, MAPA = PIEZAS[cual]
leaf = next(l for l in leaves(d["m5"]) if l["tipo"] == "hoja" and l["n"] == nL and l["j"] == jL)
nf, jf = tuple(leaf["n"]), tuple(leaf["j"]); c = leaf["cert"]
Nf = add(add(nf, mulN(2, jf)), k(1))
def nj(f):  # a + b s + c t, con s y t escritos como γ + α n + β j según MAPA
    a, b, cc = f
    (s0, sn, sj), (t0, tn, tj) = MAPA
    return (a + b * s0 + cc * t0, b * sn + cc * tn, b * sj + cc * tj)
def fmt(f):
    g, al, be = nj(f); parts = []
    if al: parts.append(("" if al == 1 else "−" if al == -1 else str(al)) + "n")
    if be: parts.append(("" if be == 1 else "−" if be == -1 else str(be)) + "j")
    s = " + ".join(parts).replace("+ −", "− ")
    if g or not parts: s = (s + (" + " if g > 0 else " − ") + str(abs(g))) if parts else str(g)
    return s.replace("+ -", "− ")
def run(segs, cfg, pos, dr, time, log):
    hist = []
    def look(x): return cfg.get(x, k(0))
    for sg in segs:
        if sg == "P":
            v = look(pos)
            der = nn(sub(sub(nf, v), k(1)))
            nv = k(0) if add(v, k(1)) == Nf else add(v, k(1))
            hist.append((pos, dr, v, der)); log.append(("paso", pos, dr, v, der))
            cfg[pos] = nv
            dr = (dr + 1) % 4 if der else (dr + 3) % 4
            pos = (pos[0] + MOV[dr][0], pos[1] + MOV[dr][1]); time = add(time, k(1))
        elif sg == "M":
            hist = []
        else:
            r = sg[1]
            cnt = {}
            for w in hist: cnt[w[0]] = cnt.get(w[0], 0) + 1
            log.append(("ciclo", list(hist), r, dict(cnt)))
            for w in hist: cfg[w[0]] = add(look(w[0]), r)
            time = add(time, mulN(len(hist), r)); hist = []
    return cfg, pos, dr, time
log0 = []
cfg, pos, dr, time = run(parse(c["pre"]), {}, (0, 0), 0, k(0), log0)
T1 = time
log = []
cfg2, pos2, dr2, time2 = run(parse(c["per"]), dict(cfg), pos, dr, k(0), log)
print("pieza", cual, "n =", nL, "j =", jL, "; periodo =", fmt(time2), "; deriva", c["deriva"])
# agrupar: pasos sueltos entre ciclos
pasos = 0; total = k(0)
for e in log:
    if e[0] == "paso":
        pasos += 1; total = add(total, k(1))
    else:
        if pasos: print(f"   {pasos:3d} pasos sueltos"); pasos = 0
        hist, r, cnt = e[1], e[2], e[3]
        L = len(hist); turns = "".join("R" if w[3] else "L" for w in hist)
        tipo = "ESPIRAL" if L == 4 and turns == "RRRR" else "escalera"
        reps = fmt(r)
        print(f"   {tipo:8s} ciclo de {L:2d} pasos ({turns}) repetido {reps} veces"
              f"  → {L}·({reps}) pasos;  casillas tocadas: {len(cnt)}, incrementos por vuelta: {sorted(cnt.values())}")
        total = add(total, mulN(L, r))
if pasos: print(f"   {pasos:3d} pasos sueltos")
print("suma comprobada:", fmt(total), "= periodo" if total == time2 else "≠ periodo")

print("\n=== Detalle de cada ciclo: qué casilla lo detiene (contador) ===")
idx = 0
for e in log:
    if e[0] != "ciclo": continue
    idx += 1
    hist, r, cnt = e[1], e[2], e[3]
    L = len(hist); turns = "".join("R" if w[3] else "L" for w in hist)
    print(f"\nciclo {idx}: {L} pasos ({turns}), repeticiones r = {fmt(r)}")
    base = hist[0][0]
    for (cel, dd, v, der) in hist:
        D = cnt[cel]
        if der: slack = sub(sub(nf, k(1)), v)
        else:   slack = sub(sub(Nf, k(2)), v)
        resto = sub(slack, mulN(D, r))     # holgura que queda tras r vueltas (≥ 0)
        ata = "  ← CONTADOR (holgura exacta 0)" if resto == k(0) else ""
        rel = (cel[0] - base[0], cel[1] - base[1])
        print(f"   casilla {str(rel):9s} lee {fmt(v):14s} gira {'R' if der else 'L'}  sube {D} por vuelta  holgura final {fmt(resto)}{ata}")
