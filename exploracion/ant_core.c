/* Núcleo rápido de la hormiga de Langton con detección y certificación de autopista.
 * Reglas: blanco -> gira derecha, negro -> gira izquierda; invierte color; avanza.
 * Direcciones: 0=N(0,1) 1=E(1,0) 2=S(0,-1) 3=O(-1,0).
 *
 * Autopista: desplazamiento pos[t+104]-pos[t] constante y no nulo.
 * Certificada: tras el inicio, la hormiga sale de la caja de todas las casillas
 * visitadas antes del inicio (más un margen) sin romper la autopista; a partir de
 * ahí solo encuentra territorio blanco y su propio rastro periódico.
 */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define W 8192
#define H (W/2)
#define P 104
#define MARGIN 6

static uint8_t *G = NULL;
static int32_t *PX = NULL, *PY = NULL, *NB = NULL;
static long CAP = 0;

static const int DX[4] = {0, 1, 0, -1};
static const int DY[4] = {1, 0, -1, 0};

/* out[0]=inicio (-1 sin autopista, -2 salió de la rejilla)
 * out[1]=dx out[2]=dy de la autopista por periodo
 * out[3]=pasos simulados out[4]=casillas negras al inicio de la autopista
 * out[5]=ancho de la caja del caos  out[6]=alto de la caja del caos */
int run_ant(int n, const int *xs, const int *ys, int x0, int y0, int d0,
            long maxsteps, long *out)
{
    if (!G) { G = (uint8_t*)calloc((size_t)W * W, 1); if (!G) return -9; }
    if (maxsteps + 2 > CAP) {
        CAP = maxsteps + 2;
        PX = (int32_t*)realloc(PX, CAP * sizeof(int32_t));
        PY = (int32_t*)realloc(PY, CAP * sizeof(int32_t));
        NB = (int32_t*)realloc(NB, CAP * sizeof(int32_t));
        if (!PX || !PY || !NB) return -9;
    }
    long nblack = 0;
    for (int i = 0; i < n; i++) {
        size_t k = (size_t)(ys[i] + H) * W + (xs[i] + H);
        if (!G[k]) { G[k] = 1; nblack++; }
    }
    int x = x0, y = y0, d = d0;
    PX[0] = x; PY[0] = y; NB[0] = (int32_t)nblack;
    long run = 0; int vx = 0, vy = 0;
    long onset = -1, t;
    int cert_minx = 0, cert_maxx = 0, cert_miny = 0, cert_maxy = 0, have_box = 0;
    long result = -1;
    for (t = 1; t <= maxsteps; t++) {
        size_t k = (size_t)(y + H) * W + (x + H);
        if (G[k]) { d = (d + 3) & 3; G[k] = 0; nblack--; }
        else      { d = (d + 1) & 3; G[k] = 1; nblack++; }
        x += DX[d]; y += DY[d];
        if (x <= -H + 2 || x >= H - 2 || y <= -H + 2 || y >= H - 2) { result = -2; break; }
        PX[t] = x; PY[t] = y; NB[t] = (int32_t)nblack;
        if (t >= P) {
            int cx = x - PX[t - P], cy = y - PY[t - P];
            if (run > 0 && cx == vx && cy == vy) run++;
            else { run = 1; vx = cx; vy = cy; have_box = 0; }
            if ((vx || vy) && run >= 30 * P) {
                long s0 = t - run + 1;
                long on = s0 - P; if (on < 0) on = 0;
                if (!have_box) {
                    int mnx = PX[0], mxx = PX[0], mny = PY[0], mxy = PY[0];
                    for (long s = 0; s <= on; s++) {
                        if (PX[s] < mnx) mnx = PX[s]; if (PX[s] > mxx) mxx = PX[s];
                        if (PY[s] < mny) mny = PY[s]; if (PY[s] > mxy) mxy = PY[s];
                    }
                    for (int i = 0; i < n; i++) {
                        if (xs[i] < mnx) mnx = xs[i]; if (xs[i] > mxx) mxx = xs[i];
                        if (ys[i] < mny) mny = ys[i]; if (ys[i] > mxy) mxy = ys[i];
                    }
                    cert_minx = mnx - MARGIN; cert_maxx = mxx + MARGIN;
                    cert_miny = mny - MARGIN; cert_maxy = mxy + MARGIN;
                    have_box = 1;
                }
                if (x < cert_minx || x > cert_maxx || y < cert_miny || y > cert_maxy) {
                    onset = on; result = on;
                    out[5] = cert_maxx - cert_minx - 2 * MARGIN + 1;
                    out[6] = cert_maxy - cert_miny - 2 * MARGIN + 1;
                    break;
                }
            }
        }
    }
    out[0] = result; out[1] = vx; out[2] = vy;
    out[3] = (t > maxsteps) ? maxsteps : t;
    out[4] = (onset >= 0) ? NB[onset] : nblack;
    /* limpiar la rejilla: borrar todo lo tocado */
    long last = (t > maxsteps) ? maxsteps : t;
    for (long s = 0; s <= last && s < CAP; s++) {
        int px = PX[s], py = PY[s];
        if (px > -H && px < H && py > -H && py < H) G[(size_t)(py + H) * W + (px + H)] = 0;
    }
    for (int i = 0; i < n; i++) G[(size_t)(ys[i] + H) * W + (xs[i] + H)] = 0;
    if (result == -2) memset(G, 0, (size_t)W * W);
    return 0;
}
