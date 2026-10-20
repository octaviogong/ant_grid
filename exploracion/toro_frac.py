from math import gcd
D = [(0,1),(1,0),(0,-1),(-1,0)]
def seq(N, M):
    B = set(); x = y = d = 0; c = []
    while True:
        b = (x, y) in B; c.append(int(b))
        if b: d = (d + 3) % 4; B.remove((x, y))
        else: d = (d + 1) % 4; B.add((x, y))
        x = (x + D[d][0]) % M; y = (y + D[d][1]) % N
        if not B and x == 0 and y == 0 and d == 0: return c
for N, M in [(1,2), (2,2), (2,3), (3,3), (3,7), (4,4)]:
    c = seq(N, M); P = len(c); R = int("".join(map(str, c)), 2); den = 2**P - 1; g = gcd(R, den)
    print(f"{N}x{M}: P={P}  x = {R//g}/{den//g}" if P <= 20 else f"{N}x{M}: P={P}  denominador reducido = (2^{P}-1)/{g}")
