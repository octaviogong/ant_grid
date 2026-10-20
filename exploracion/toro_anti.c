/* Antiperiodicidad en toros grandes: guarda la sucesión de colores y compara mitades. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int N = atoi(argv[1]), M = atoi(argv[2]); unsigned long long cap = strtoull(argv[3], 0, 10);
    const int DX[4] = {0,1,0,-1}, DY[4] = {1,0,-1,0};
    uint8_t *c = malloc(cap); uint64_t B = 0; int x = 0, y = 0, d = 0; unsigned long long t = 0;
    do {
        uint64_t bit = 1ULL << (y * M + x); int b = (B & bit) != 0; c[t] = b;
        d = b ? (d + 3) & 3 : (d + 1) & 3; B ^= bit;
        x += DX[d]; if (x < 0) x += M; else if (x >= M) x -= M;
        y += DY[d]; if (y < 0) y += N; else if (y >= N) y -= N;
        t++;
    } while (!(B == 0 && x == 0 && y == 0 && d == 0) && t < cap);
    if (t >= cap) { printf("%dx%d: >%llu\n", N, M, cap); return 0; }
    unsigned long long h = t / 2; int anti = 1;
    for (unsigned long long i = 0; i < h; i++) if (c[i + h] != 1 - c[i]) { anti = 0; break; }
    printf("%dx%d: periodo=%llu antiperiodico=%d\n", N, M, t, anti);
    return 0;
}
