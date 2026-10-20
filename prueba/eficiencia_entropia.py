"""1) ¿Qué tan eficientes son las autopistas? Velocidad = casillas recorridas en línea recta por paso.
   2) Entropía de la traza (colores leídos) antes y después de la autopista."""
import json, math
from collections import Counter
# --- 1. velocidades de las 474 autopistas del catálogo (reglas de 2 a 12 colores, desde el blanco)
cat = json.load(open("../exploracion/pendientes.json"))
rows = []
for rule, v in cat.items():
    dx, dy = v["v"]; P = v["P"]
    rows.append((abs(dx) + abs(dy)) / P)
rows.sort()
print(f"autopistas en el catálogo: {len(rows)}")
print(f"velocidad (|dx|+|dy|)/P: mínima {rows[0]:.4f}, mediana {rows[len(rows)//2]:.4f}, máxima {rows[-1]:.4f}")
fast = sorted(cat.items(), key=lambda kv: -(abs(kv[1]['v'][0]) + abs(kv[1]['v'][1])) / kv[1]['P'])[:3]
print("más rápidas:", [(r, v['P'], v['v']) for r, v in fast])
print(f"Langton RL: 4/104 = {4/104:.4f}   (máximo teórico para una hormiga que gira en cada paso: 1)")
# --- 2. entropía de la traza de RL en ventanas
D = [(0, 1), (1, 0), (0, -1), (-1, 0)]
B = set(); x = y = 0; d = 0; tr = []
for t in range(16000):
    c = 1 if (x, y) in B else 0; tr.append(c)
    d = (d + 3) % 4 if c else (d + 1) % 4
    B ^= {(x, y)}; x += D[d][0]; y += D[d][1]
def H(seq, k=10):
    cnt = Counter(tuple(seq[i:i + k]) for i in range(len(seq) - k + 1))
    tot = sum(cnt.values())
    return -sum(c / tot * math.log2(c / tot) for c in cnt.values())
print("\nentropía por bloques de 10 colores leídos (máximo posible 10 bits), ventanas de 2 000 pasos:")
for s in range(0, 16000, 2000):
    print(f"   pasos {s:5d}-{s+1999:5d}: {H(tr[s:s+2000]):5.2f} bits   distintos bloques: {len(set(tuple(tr[i:i+10]) for i in range(s, s+1990)))}")
