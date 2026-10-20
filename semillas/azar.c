/* Hormiga generalizada (N colores, tabla de giros) con:
 *  - configuración inicial arbitraria (celdas con color), posición y dirección iniciales;
 *  - detección de autopista (desplazamiento constante cada P pasos durante max(40P, 4000) pasos)
 *    y confirmación: la hormiga sale de la caja de todo lo visitado antes del inicio;
 *  - conteo de casillas distintas visitadas hasta el inicio de la autopista;
 *  - foto opcional de las casillas no nulas cerca de la hormiga en un paso dado.
 * Rejilla de 4096 x 4096 con origen al centro.
 */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define W 4096
#define H (W/2)
#define PMAX 3000
#define MARGIN 8

static uint8_t *G = NULL, *VIS = NULL;
static int32_t *PX = NULL, *PY = NULL, *NEWT = NULL;
static long CAP = 0;
static const int DX[4] = {0, 1, 0, -1}, DY[4] = {1, 0, -1, 0};

static long detect(long T, int *Pout, int *vx, int *vy) {
    for (int P = 1; P <= PMAX; P++) {
        long Wn = 40L * P; if (Wn < 4000) Wn = 4000;
        if (T < Wn + P) break;
        int ax = PX[T] - PX[T - P], ay = PY[T] - PY[T - P];
        if (!ax && !ay) continue;
        if (PX[T-1] - PX[T-1-P] != ax || PY[T-1] - PY[T-1-P] != ay) continue;
        if (PX[T-7] - PX[T-7-P] != ax || PY[T-7] - PY[T-7-P] != ay) continue;
        int ok = 1;
        for (long s = T - Wn; s <= T; s++)
            if (PX[s] - PX[s-P] != ax || PY[s] - PY[s-P] != ay) { ok = 0; break; }
        if (!ok) continue;
        long s = T - Wn;
        while (s - P >= 0 && PX[s] - PX[s-P] == ax && PY[s] - PY[s-P] == ay) s--;
        long on = s - P + 1; if (on < 0) on = 0;
        *Pout = P; *vx = ax; *vy = ay;
        return on;
    }
    return -1;
}

/* out: [0]=inicio (-1 sin autopista, -2 borde) [1]=P [2]=dx [3]=dy [4]=casillas distintas hasta el inicio
 *      [5]=pasos simulados [6]=número de casillas en la foto
 * foto: si snap_t >= 0, guarda en sx,sy,sc las casillas no nulas a distancia <= snap_r de la hormiga
 *       en el paso snap_t (coordenadas relativas a la hormiga), y en out[7] la dirección de la hormiga. */
int correr(int N, const int *turns, int n0, const int *x0s, const int *y0s, const int *c0s,
           int ax0, int ay0, int ad0, long maxsteps, long snap_t, int snap_r,
           int *sx, int *sy, int *sc, int snap_cap, long *out)
{
    if (!G) { G = calloc((size_t)W * W, 1); VIS = calloc((size_t)W * W, 1); if (!G || !VIS) return -9; }
    if (maxsteps + 2 > CAP) {
        CAP = maxsteps + 2;
        PX = realloc(PX, CAP * sizeof(int32_t)); PY = realloc(PY, CAP * sizeof(int32_t));
        NEWT = realloc(NEWT, CAP * sizeof(int32_t));
        if (!PX || !PY || !NEWT) return -9;
    }
    for (int i = 0; i < n0; i++) G[(size_t)(y0s[i] + H) * W + (x0s[i] + H)] = (uint8_t)c0s[i];
    int x = ax0, y = ay0, d = ad0;
    long t = 0, nnew = 0, result = -1, onset = -1;
    int P = 0, vx = 0, vy = 0, haveP = 0;
    int bminx = 0, bmaxx = 0, bminy = 0, bmaxy = 0;
    PX[0] = x; PY[0] = y;
    { size_t k = (size_t)(y + H) * W + (x + H); VIS[k] = 1; NEWT[nnew++] = 0; }
    out[6] = 0;
    long nextcheck = 4000;
    while (t < maxsteps) {
        if (t == snap_t) {
            int cnt = 0;
            for (int yy = y - snap_r; yy <= y + snap_r; yy++)
                for (int xx = x - snap_r; xx <= x + snap_r; xx++) {
                    uint8_t c = G[(size_t)(yy + H) * W + (xx + H)];
                    if (c && cnt < snap_cap) { sx[cnt] = xx - x; sy[cnt] = yy - y; sc[cnt] = c; cnt++; }
                }
            out[6] = cnt; out[7] = d;
        }
        size_t k = (size_t)(y + H) * W + (x + H);
        int c = G[k];
        d = turns[c] ? (d + 1) & 3 : (d + 3) & 3;
        G[k] = (uint8_t)((c + 1) % N);
        x += DX[d]; y += DY[d]; t++;
        PX[t] = x; PY[t] = y;
        if (x <= -H + 4 || x >= H - 4 || y <= -H + 4 || y >= H - 4) { result = -2; break; }
        size_t k2 = (size_t)(y + H) * W + (x + H);
        if (!VIS[k2]) { VIS[k2] = 1; NEWT[nnew++] = (int32_t)t; }
        if (!haveP && t >= nextcheck) {
            nextcheck = t + 4000;
            long on = detect(t, &P, &vx, &vy);
            if (on >= 0) {
                haveP = 1; onset = on;
                bminx = bmaxx = PX[0]; bminy = bmaxy = PY[0];
                for (long s = 0; s <= on; s++) {
                    if (PX[s] < bminx) bminx = PX[s]; if (PX[s] > bmaxx) bmaxx = PX[s];
                    if (PY[s] < bminy) bminy = PY[s]; if (PY[s] > bmaxy) bmaxy = PY[s];
                }
                for (int i = 0; i < n0; i++) {
                    if (x0s[i] < bminx) bminx = x0s[i]; if (x0s[i] > bmaxx) bmaxx = x0s[i];
                    if (y0s[i] < bminy) bminy = y0s[i]; if (y0s[i] > bmaxy) bmaxy = y0s[i];
                }
                bminx -= MARGIN; bmaxx += MARGIN; bminy -= MARGIN; bmaxy += MARGIN;
            }
        }
        if (haveP) {
            /* la autopista debe seguir intacta hasta salir de la caja */
            if (t >= P && (PX[t] - PX[t-P] != vx || PY[t] - PY[t-P] != vy)) { haveP = 0; onset = -1; nextcheck = t + 4000; continue; }
            if ((x < bminx || x > bmaxx || y < bminy || y > bmaxy) && (snap_t < 0 || t > snap_t)) { result = onset; break; }
        }
    }
    out[0] = result; out[1] = P; out[2] = vx; out[3] = vy; out[5] = t;
    long cntv = 0;
    if (result >= 0) {   /* casillas distintas visitadas hasta el inicio */
        long lo = 0, hi = nnew;
        while (lo < hi) { long mid = (lo + hi) / 2; if (NEWT[mid] <= result) lo = mid + 1; else hi = mid; }
        cntv = lo;
    }
    out[4] = cntv;
    /* limpiar */
    for (long s = 0; s <= t; s++) {
        int px = PX[s], py = PY[s];
        if (px > -H && px < H && py > -H && py < H) { size_t kk = (size_t)(py + H) * W + (px + H); G[kk] = 0; VIS[kk] = 0; }
    }
    for (int i = 0; i < n0; i++) G[(size_t)(y0s[i] + H) * W + (x0s[i] + H)] = 0;
    if (result == -2) { memset(G, 0, (size_t)W * W); memset(VIS, 0, (size_t)W * W); }
    return 0;
}
