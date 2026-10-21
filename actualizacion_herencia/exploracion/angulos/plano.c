/* Hormiga generalizada en el plano desde el tablero en blanco.
   Uso: ./plano T Pmax < reglas   (una regla R/L por línea, hasta 127 estados)
   Salida: regla pasos autopista P dx dy inicio celdas_visitadas max_visitas_por_celda
   Autopista: p(t+P)-p(t) constante y no nula en la ventana final de max(30P,20000) pasos
   (el mismo criterio del catálogo). 'inicio' = primer t desde el que se repite. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define W 8192
#define H (W/2)
int main(int argc,char**argv){
  long T=atol(argv[1]); int Pmax=atoi(argv[2]);
  uint8_t *G=calloc((size_t)W*W,1); uint16_t *V=calloc((size_t)W*W,2);
  int32_t *px=malloc(sizeof(int32_t)*(T+2)), *py=malloc(sizeof(int32_t)*(T+2));
  uint32_t *touched=malloc(sizeof(uint32_t)*(T+2));
  int DX[4]={0,1,0,-1}, DY[4]={1,0,-1,0}; char w[256];
  while(scanf("%255s",w)==1){
    int N=strlen(w); int x=0,y=0,d=0; long t, nt=0, vis=0; int K=0;
    px[0]=0; py[0]=0;
    for(t=1;t<=T;t++){
      uint32_t k=(uint32_t)(y+H)*W+(uint32_t)(x+H);
      uint8_t g=G[k]; int c=g&127;
      if(!(g&128)){ touched[nt++]=k; vis++; }
      if(V[k]<65535) V[k]++; if(V[k]>K) K=V[k];
      d=(d+(w[c]=='R'?1:3))&3;
      G[k]=(uint8_t)(128|((c+1)%N));
      x+=DX[d]; y+=DY[d]; px[t]=x; py[t]=y;
      if(x<=-H+2||x>=H-2||y<=-H+2||y>=H-2){ t++; break; }
    }
    long n=t-1; int hw=0,bP=0,bx=0,by=0; long onset=-1;
    for(int P=1;P<=Pmax && !hw;P++){
      long Wn=30L*P; if(Wn<20000)Wn=20000;
      if(n<Wn+P) break;
      int vx=px[n]-px[n-P], vy=py[n]-py[n-P];
      if(!vx&&!vy) continue;
      if(px[n-1]-px[n-1-P]!=vx||py[n-7]-py[n-7-P]!=vy) continue;
      int ok=1;
      for(long i=n-Wn;i<=n;i++) if(px[i]-px[i-P]!=vx||py[i]-py[i-P]!=vy){ok=0;break;}
      if(ok){ long s=n-Wn; while(s-P>=0&&px[s]-px[s-P]==vx&&py[s]-py[s-P]==vy) s--;
        hw=1;bP=P;bx=vx;by=vy;onset=s-P+1; }
    }
    printf("%s %ld %d %d %d %d %ld %ld %d\n",w,n,hw,bP,bx,by,onset,vis,K); fflush(stdout);
    for(long i=0;i<nt;i++){ G[touched[i]]=0; V[touched[i]]=0; }
  }
}
