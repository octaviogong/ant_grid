import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import RegularPolygon
from dividendo import F, dividendo
k = 9976 + 104 * 50
S0 = dividendo(k)
S1 = F(S0, k - 9976)
S2 = F(S1, 9976)
xs = [c[0] for c in S0[0]]; ys = [c[1] for c in S0[0]]
x0, x1, y0, y1 = min(xs) - 4, max(xs) + 4, min(ys) - 4, max(ys) + 4
titulos = [f"Paso 0: el «dividendo» ({len(S0[0])} negras)",
           f"Paso {k - 9976:,}: se comió la autopista ({len(S1[0])} negras)".replace(",", ","),
           f"Paso {k:,}: tablero en blanco ({len(S2[0])} negras)"]
fig, axs = plt.subplots(3, 1, figsize=(5.2, 12.5), dpi=150)
for ax, S, t in zip(axs, (S0, S1, S2), titulos):
    ax.set_facecolor("white")
    for (x, y) in S[0]:
        ax.add_patch(plt.Rectangle((x - 0.5, y - 0.5), 1, 1, color="#1f1f1f", lw=0))
    (ax_, ay), d = S[1], S[2]
    ax.add_patch(RegularPolygon((ax_, ay), 3, radius=2.6, orientation=[0, -1.5708, 3.1416, 1.5708][d],
                                color="#d62728", zorder=5))
    ax.set_xlim(x0, x1); ax.set_ylim(y0, y1); ax.set_aspect("equal")
    ax.set_xticks([]); ax.set_yticks([])
    for s in ax.spines.values(): s.set_color("#999999")
    ax.set_title(t, fontsize=10.5)
fig.suptitle("Un tablero que termina en blanco\n(la hormiga es el triángulo rojo)", fontsize=12)
fig.tight_layout()
fig.savefig("dividendo.png", facecolor="white")
print(len(S0[0]), len(S1[0]), len(S2[0]), S2[1], S2[2])
