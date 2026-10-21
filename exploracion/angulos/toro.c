/* Cobertura en un toro n x n desde el tablero en blanco.
   Entrada: una regla por línea (R/L). Salida: regla t50 t90 t100 (pasos; -1 si no se alcanza en T). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){
  int n=atoi(argv[1]); long T=atol(argv[2]);
  unsigned char *s=malloc(n*n), *vis=malloc(n*n); char w[64];
  int dx[4]={0,1,0,-1}, dy[4]={1,0,-1,0};
  while(scanf("%63s",w)==1){
    int N=strlen(w); memset(s,0,n*n); memset(vis,0,n*n);
    int x=0,y=0,h=0; long cnt=0,t50=-1,t90=-1,t100=-1, tot=(long)n*n;
    for(long t=0;t<T;t++){
      int i=y*n+x;
      if(!vis[i]){vis[i]=1;cnt++;
        if(t50<0&&2*cnt>=tot)t50=t; if(t90<0&&10*cnt>=9*tot)t90=t; if(cnt==tot){t100=t;break;}}
      int c=s[i]; h=(w[c]=='R')?(h+1)&3:(h+3)&3; s[i]=(c+1)%N;
      x=(x+dx[h]+n)%n; y=(y+dy[h]+n)%n;
    }
    printf("%s %ld %ld %ld %ld\n",w,t50,t90,t100,cnt);
  }
}
