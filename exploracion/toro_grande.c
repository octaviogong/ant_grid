/* Toro grande L x L: episodios de autopista (desplazamiento ±2,±2 cada 104 pasos sostenido).
 * Para cada episodio: inicio, duración y cuántas veces dio la vuelta al toro antes de romperse. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int L = atoi(argv[1]); long T = atol(argv[2]);
    const int DX[4] = {0,1,0,-1}, DY[4] = {1,0,-1,0};
    uint8_t *G = calloc((size_t)L * L, 1);
    long long *ux = malloc(sizeof(long long) * (T + 1)), *uy = malloc(sizeof(long long) * (T + 1));
    int x = 0, y = 0, d = 0; ux[0] = uy[0] = 0;
    long run = 0, ep = 0, steps_hw = 0; int vx = 0, vy = 0; long eps_start = -1;
    long long blank_times = 0, nb = 0;
    for (long t = 1; t <= T; t++) {
        size_t k = (size_t)y * L + x;
        if (G[k]) { d = (d + 3) & 3; G[k] = 0; nb--; } else { d = (d + 1) & 3; G[k] = 1; nb++; }
        if (nb == 0) blank_times++;
        x += DX[d]; if (x < 0) x += L; else if (x >= L) x -= L;
        y += DY[d]; if (y < 0) y += L; else if (y >= L) y -= L;
        ux[t] = ux[t-1] + DX[d]; uy[t] = uy[t-1] + DY[d];
        if (t >= 104) {
            int cx = (int)(ux[t] - ux[t-104]), cy = (int)(uy[t] - uy[t-104]);
            int diag = (cx == 2 || cx == -2) && (cy == 2 || cy == -2);
            if (diag && run > 0 && cx == vx && cy == vy) run++;
            else {
                if (run >= 20 * 104) {
                    long s = t - run - 104; double dist = (double)(run + 104) / 104.0 * 2.0;
                    ep++; steps_hw += run + 104;
                    if (ep <= 12) printf("  episodio %ld: inicio=%ld duracion=%ld pasos (%.1f periodos) vueltas_al_toro=%.2f\n",
                                         ep, s, run + 104, (run + 104) / 104.0, dist / L);
                }
                run = diag ? 1 : 0; vx = cx; vy = cy;
            }
        }
    }
    printf("toro %dx%d, %ld pasos: episodios de autopista=%ld, fraccion del tiempo en autopista=%.3f, veces que el tablero quedo en blanco=%lld\n",
           L, L, T, ep, (double)steps_hw / T, blank_times);
    return 0;
}
