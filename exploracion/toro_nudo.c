/* Números de enrollamiento: posición "desenrollada" de la hormiga al cerrar la órbita en un toro N x M.
 * Desplazamiento total = (a·M, b·N): el bucle da a vueltas horizontales y b verticales (clase (a,b)).
 * También registra cuándo la órbita pasa por el tablero completamente blanco y por el negro. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int N = atoi(argv[1]), M = atoi(argv[2]); unsigned long long cap = strtoull(argv[3], 0, 10);
    const int DX[4] = {0,1,0,-1}, DY[4] = {1,0,-1,0};
    uint64_t B = 0, FULL = (N * M == 64) ? ~0ULL : ((1ULL << (N * M)) - 1);
    int x = 0, y = 0, d = 0; long long ux = 0, uy = 0; unsigned long long t = 0, blancos = 0, negros = 0;
    do {
        uint64_t bit = 1ULL << (y * M + x);
        d = (B & bit) ? (d + 3) & 3 : (d + 1) & 3; B ^= bit;
        ux += DX[d]; uy += DY[d];
        x += DX[d]; if (x < 0) x += M; else if (x >= M) x -= M;
        y += DY[d]; if (y < 0) y += N; else if (y >= N) y -= N;
        t++;
        if (B == 0) blancos++;
        if (B == FULL) negros++;
    } while (!(B == 0 && x == 0 && y == 0 && d == 0) && t < cap);
    if (t >= cap) { printf("%dx%d >%llu\n", N, M, cap); return 0; }
    printf("%dx%d periodo=%llu desplazamiento=(%lld,%lld) vueltas=(%lld,%lld) veces_en_blanco=%llu veces_en_negro=%llu\n",
           N, M, t, ux, uy, ux / M, uy / N, blancos, negros);
    return 0;
}
