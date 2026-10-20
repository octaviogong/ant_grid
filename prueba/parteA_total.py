"""Parte A completa: n >= m - 1, m >= 5, con división automática de casos."""
import sys, json
from collections import Counter
from simbolico import Cone, fmtc
from division_casos import prove_region
regiones = [Cone((4, 1, 2), (2, 0, 1), "n >= m-1, m >= 5")]   # j = 2 + t, n = 2j + s
for R in regiones:
    res = prove_region(R)
    print(R.nombre, "→ piezas:", len(res), dict(Counter(st for _, st, _ in res)))
    for Rr, st, r in res:
        if st != "ok": print("   ", st, Rr.nombre, "n=", fmtc(Rr.n()), "j=", fmtc(Rr.j()), (r or {}).get("motivo", ""))
    json.dump([dict(estado=st, n=Rr.n(), j=Rr.j(), ruta=Rr.nombre, P=(r or {}).get("P")) for Rr, st, r in res],
              open("parteA_piezas.json", "w"), ensure_ascii=False, indent=0)
