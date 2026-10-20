/* Pasos hasta volver EXACTAMENTE al estado inicial (tablero vacío, origen, marco inicial). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define R 64
int main(int argc, char **argv) {
    int d = atoi(argv[1]); const char *rule = argv[2]; long cap = atol(argv[3]);
    int n = strlen(rule), ax[16], sg[16];
    for (int i = 0; i < n; i++) {
        char c = rule[i];
        ax[i] = (c=='R'||c=='L') ? 1 : (c=='U'||c=='D') ? 2 : 3;
        sg[i] = (c=='R'||c=='U'||c=='W') ? 1 : -1;
    }
    long side = 2 * R + 1, cells = 1; for (int i = 0; i < d; i++) cells *= side;
    uint8_t *G = calloc(cells, 1); int p[4] = {0}, frame[4], f0[4];
    for (int i = 0; i < d; i++) frame[i] = f0[i] = i + 1;
    long nz = 0, t; int maxr = 0;
    for (t = 1; t <= cap; t++) {
        long idx = 0; for (int i = d - 1; i >= 0; i--) idx = idx * side + (p[i] + R);
        int col = G[idx], a = ax[col], s = sg[col], f = frame[0], e = frame[a];
        frame[0] = s * e; frame[a] = -s * f;
        int nc = (col + 1) % n; nz += (nc != 0) - (col != 0); G[idx] = nc;
        int fa = abs(frame[0]) - 1; p[fa] += frame[0] > 0 ? 1 : -1;
        if (abs(p[fa]) > maxr) maxr = abs(p[fa]);
        if (maxr >= R) { printf("%dD %s: se salió del radio %d\n", d, rule, R); return 0; }
        if (nz == 0) {
            int ok = 1; for (int i = 0; i < d; i++) if (p[i] || frame[i] != f0[i]) ok = 0;
            if (ok) { printf("%dD %s: vuelve al tablero vacío en %ld pasos (radio máximo %d)\n", d, rule, t, maxr); return 0; }
        }
    }
    printf("%dD %s: no volvió en %ld pasos (radio máximo %d)\n", d, rule, cap, maxr); return 0;
}
