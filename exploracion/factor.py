import random, math
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def rho(n):
    if n % 2 == 0: return 2
    while True:
        c = random.randrange(1, n); f = lambda x: (x * x + c) % n
        x = y = random.randrange(2, n); d = 1
        while d == 1: x = f(x); y = f(f(y)); d = math.gcd(abs(x - y), n)
        if d != n: return d
def factor(n):
    if n == 1: return []
    if is_prime(n): return [n]
    for p in range(2, 10000):
        if n % p == 0: return [p] + factor(n // p)
    d = rho(n); return sorted(factor(d) + factor(n // d))
D = (2**104 - 1) // 5
print("D =", D)
print("D =", " · ".join(map(str, factor(D))))
print("2^104-1 =", " · ".join(map(str, factor(2**104 - 1))))
