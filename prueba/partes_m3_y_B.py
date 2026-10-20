import json, sys
from collections import Counter
from simbolico import Cone, fmtc, ZERO
from division_casos import prove_region, law
def report(nombre, res, archivo):
    print(nombre, "→ piezas:", len(res), dict(Counter(st for _, st, _ in res)), flush=True)
    for Rr, st, r in res:
        tag = "" if st == "ok" else "  <<"
        print(f"   {st:17s} n={fmtc(Rr.n()):14s} j={fmtc(Rr.j()):10s} P={fmtc(r['P']) if r and r.get('ok') else '-':16s} deriva={r.get('deriva') if r else None}"
              + (f" inicio<={fmtc(r['inicio'])}" if r and r.get('ok') else f" {(r or {}).get('motivo','')}") + tag, flush=True)
    json.dump([dict(estado=st, n=Rr.n(), j=Rr.j(), P=(r or {}).get("P"), inicio=(r or {}).get("inicio"), deriva=(r or {}).get("deriva")) for Rr, st, r in res],
              open(archivo, "w"), indent=0)
which = sys.argv[1]
if which == "A3":
    res = prove_region(Cone((3, 1, 0), (1, 0, 0), "A: m = 3, n >= 3"))
    report("Parte A, m = 3", res, "parteA_m3.json")
if which == "B":
    blank = lambda R: ({}, (0, 0), 0)
    res = prove_region(Cone((4, 1, 2), (2, 0, 1), "B: n >= m-1, m >= 5"), seed=blank, budget=[3000])
    report("Parte B (desde blanco), m >= 5", res, "parteB.json")
if which == "B3":
    blank = lambda R: ({}, (0, 0), 0)
    res = prove_region(Cone((3, 1, 0), (1, 0, 0), "B: m = 3, n >= 3"), seed=blank)
    report("Parte B (desde blanco), m = 3", res, "parteB_m3.json")
