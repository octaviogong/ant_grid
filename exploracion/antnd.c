/* Hormiga de Langton en d dimensiones (d = 2, 3, 4) con n colores.
 * La hormiga lleva un marco ortonormal: frame[0] = adelante, frame[1..d-1] = ejes del cuerpo
 * (derecha, arriba, w...). Cada eje se guarda como entero con signo: ±(k+1) = ±e_k del mundo.
 * Regla: turn_axis[c] in 1..d-1 y turn_sign[c] = ±1. Al pisar color c, gira 90° hacia
 * turn_sign·frame[axis]:  adelante' = s·eje,  eje' = −s·adelante  (rotación propia).
 * Luego el color pasa a (c+1) mod n y avanza una casilla.
 * Tablero disperso: tabla hash con direccionamiento abierto, coordenadas de 16 bits.
 * Devuelve la trayectoria completa en traj[t*d + k]. */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static uint64_t *KEYS = NULL; static uint8_t *VALS = NULL; static uint64_t CAPM = 0;
#define EMPTY 0xFFFFFFFFFFFFFFFFULL

static inline uint64_t pack(const int *p, int d) {
    uint64_t k = 0;
    for (int i = 0; i < d; i++) k = (k << 16) | (uint64_t)((p[i] + 32768) & 0xFFFF);
    return k;
}
static inline uint64_t hsh(uint64_t k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33;
    return k;
}
static inline uint8_t *slot(uint64_t key) {
    uint64_t i = hsh(key) & CAPM;
    while (KEYS[i] != EMPTY && KEYS[i] != key) i = (i + 1) & CAPM;
    if (KEYS[i] == EMPTY) { KEYS[i] = key; VALS[i] = 0; }
    return &VALS[i];
}

/* init: n_init celdas con sus colores (coords en init_xyz[i*d+k], color en init_c[i]) */
long run_nd(int d, int n, const int *turn_axis, const int *turn_sign, long maxsteps,
            int n_init, const int *init_xyz, const int *init_c, int32_t *traj)
{
    uint64_t need = 1; while (need < (uint64_t)(maxsteps + n_init) * 3) need <<= 1;
    if (need < (1u << 20)) need = 1u << 20;
    if (need - 1 != CAPM) {
        free(KEYS); free(VALS);
        KEYS = malloc(need * sizeof(uint64_t)); VALS = malloc(need);
        if (!KEYS || !VALS) return -9;
        CAPM = need - 1;
    }
    memset(KEYS, 0xFF, (CAPM + 1) * sizeof(uint64_t));
    int p[4] = {0, 0, 0, 0}, frame[4];
    for (int i = 0; i < d; i++) frame[i] = i + 1;          /* adelante = +e0, ejes = +e1.. */
    /* en 2D: adelante = norte (+y), derecha = este (+x) para coincidir con la hormiga plana */
    if (d == 2) { frame[0] = 2; frame[1] = 1; }
    for (int i = 0; i < n_init; i++) *slot(pack(&init_xyz[i * d], d)) = (uint8_t)init_c[i];
    long t;
    for (int k = 0; k < d; k++) traj[k] = 0;
    for (t = 1; t <= maxsteps; t++) {
        uint8_t *c = slot(pack(p, d));
        int col = *c, ax = turn_axis[col], s = turn_sign[col];
        int f = frame[0], e = frame[ax];
        frame[0] = s * e; frame[ax] = -s * f;
        *c = (uint8_t)((col + 1) % n);
        int fa = frame[0] > 0 ? frame[0] - 1 : -frame[0] - 1, fs = frame[0] > 0 ? 1 : -1;
        p[fa] += fs;
        if (p[fa] > 32000 || p[fa] < -32000) { t--; break; }
        for (int k = 0; k < d; k++) traj[t * d + k] = p[k];
    }
    return t > maxsteps ? maxsteps : t;
}
