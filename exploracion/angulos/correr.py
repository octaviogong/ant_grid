"""Corre ./plano y ./toro en paralelo (2 procesos) sobre una lista de reglas."""
import subprocess, sys
def run(cmd, rules, nproc=2):
    rules=list(dict.fromkeys(rules))
    chunks=[rules[i::nproc] for i in range(nproc)]
    ps=[subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) for _ in chunks]
    for p,c in zip(ps,chunks): p.stdin.write('\n'.join(c)+'\n'); p.stdin.close()
    out={}
    for p in ps:
        for l in p.stdout: f=l.split(); out[f[0]]=f[1:]
        p.wait()
    return out
def plano(rules,T=5_000_000,Pmax=6000):
    o=run(['./plano',str(T),str(Pmax)],rules)
    return {w:dict(pasos=int(v[0]),hw=v[1]=='1',P=int(v[2]),d=(int(v[3]),int(v[4])),inicio=int(v[5]),vis=int(v[6]),K=int(v[7])) for w,v in o.items()}
def toro(rules,n=128,T=4_000_000):
    o=run(['./toro',str(n),str(T)],rules)
    return {w:dict(t50=int(v[0]),t90=int(v[1]),t100=int(v[2]),cub=int(v[3])) for w,v in o.items()}
