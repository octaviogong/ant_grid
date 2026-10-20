/* Hormiga de Langton en un toro N x M (tablero finito con bordes que se enrollan).
 * Como la regla es reversible y los estados son finitos, la órbita es puramente periódica:
 * se cuenta cuántos pasos tarda en volver al estado inicial (tablero blanco, (0,0), norte). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int N = atoi(argv[1]), M = atoi(argv[2]);
    unsigned long long cap = strtoull(argv[3], 0, 10);
    const int DX[4] = {0,1,0,-1}, DY[4] = {1,0,-1,0};
    uint64_t B = 0; int x = 0, y = 0, d = 0;
    unsigned long long t = 0, ones = 0;
    do {
        uint64_t bit = 1ULL << (y * M + x);
        if (B & bit) { d = (d + 3) & 3; ones++; } else d = (d + 1) & 3;
        B ^= bit;
        x += DX[d]; if (x < 0) x += M; else if (x >= M) x -= M;
        y += DY[d]; if (y < 0) y += N; else if (y >= N) y -= N;
        t++;
    } while (!(B == 0 && x == 0 && y == 0 && d == 0) && t < cap);
    if (B == 0 && x == 0 && y == 0 && d == 0) printf("%d %d %llu %llu\n", N, M, t, ones);
    else printf("%d %d >%llu\n", N, M, cap);
    return 0;
}
