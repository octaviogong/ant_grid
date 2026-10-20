/* Hormiga generalizada (turmita): color c -> gira según turns[c] (+1 derecha, -1 izquierda),
 * pasa al color (c+1) mod n, avanza. Devuelve la trayectoria para detectar periodos. */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 8192
#define H (W/2)
static const int DX[4]={0,1,0,-1}, DY[4]={1,0,-1,0};
long run_rule(int n, const int *turns, long maxsteps, int32_t *px, int32_t *py)
{
    uint8_t *G = (uint8_t*)calloc((size_t)W*W,1); if(!G) return -9;
    int x=0,y=0,d=0; long t;
    px[0]=0; py[0]=0;
    for(t=1;t<=maxsteps;t++){
        size_t k=(size_t)(y+H)*W+(x+H);
        int c=G[k];
        d=(d+(turns[c]>0?1:3))&3;
        G[k]=(uint8_t)((c+1)%n);
        x+=DX[d]; y+=DY[d];
        px[t]=x; py[t]=y;
        if(x<=-H+2||x>=H-2||y<=-H+2||y>=H-2){ t++; break; }
    }
    free(G);
    return t-1;
}
