"""Re-verificación de las 12 autopistas no diagonales desde el tablero blanco, con 20M pasos
(antes 3M) y simulador independiente (antnd, tablero hash). Debe repetirse P y deriva."""
import json, numpy as np
import antnd as A
prev = json.load(open("pendientes.json"))
nd = {r: v for r, v in prev.items() if abs(v["v"][0]) != abs(v["v"][1])}
for rule, v in nd.items():
    T = A.run(rule, 2, 20_000_000)
    h = A.highway(T)
    # caja de todo lo visitado antes del inicio vs. posición final: la hormiga ya salió del caos
    if h:
        pre = T[:h["inicio"] + 1]; lo, hi = pre.min(0), pre.max(0); fin = T[-1]
        fuera = bool(np.any(fin < lo - 6) or np.any(fin > hi + 6))
    print(f"{rule:14s} antes: P={v['P']:5d} deriva={tuple(v['v'])}  ahora: "
          + (f"P={h['P']:5d} deriva={h['v']} inicio={h['inicio']:,} fuera_de_la_zona_del_caos={fuera}" if h else "SIN autopista"),
          flush=True)
