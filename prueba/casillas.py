from certificado import simulate, candidate, certify
def period_cells(n, m):
    pos, dirs, _ = simulate(n, m, 80000)
    P, v, t_on = candidate(pos); t1 = certify(n, m, P, v, t_on)
    pos, dirs, snaps = simulate(n, m, t1 + P, snapshot_at=(t1,))
    V = sorted(set(pos[t1:t1 + P]))
    B1, p1, d1 = snaps[t1]
    rel = {(c[0] - p1[0], c[1] - p1[1]): B1.get(c, 0) for c in V}
    return P, v, len(V), rel, d1
for n, m in [(10, 5), (12, 5), (10, 7), (10, 9), (14, 9)]:
    P, v, k, rel, d1 = period_cells(n, m)
    xs = [c[0] for c in rel]; ys = [c[1] for c in rel]
    print(f"n={n} m={m} P={P} |V|={k} dir={d1} caja x[{min(xs)},{max(xs)}] y[{min(ys)},{max(ys)}]")
    for yy in range(max(ys), min(ys) - 1, -1):
        row = []
        for xx in range(min(xs), max(xs) + 1):
            val = rel.get((xx, yy))
            row.append(" ." if val is None else f"{val:2d}")
        print("     " + " ".join(row))
