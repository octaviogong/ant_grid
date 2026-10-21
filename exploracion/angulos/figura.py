import json, numpy as np, collections, math
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
from palabras import ALPHAS, rot
BLUE,ORANGE,AQUA,GRAY,INK,MUTED='#2a78d6','#eb6834','#1baf7a','#a3a29c','#0b0b0b','#52514e'
plt.rcParams.update({'font.size':9,'axes.edgecolor':GRAY,'axes.labelcolor':INK,'xtick.color':MUTED,'ytick.color':MUTED,
                     'axes.spines.top':False,'axes.spines.right':False,'figure.facecolor':'#fcfcfb','axes.facecolor':'#fcfcfb'})
fig,ax=plt.subplots(1,3,figsize=(13,4.1),gridspec_kw=dict(width_ratios=[1.5,1,1]))
# (a) angle scan
E=json.load(open('e2.json'))['60']; a0=ax[0]
for n in range(2,40): a0.axvspan(2/(2*n+3),1/(n+1),color=BLUE,alpha=0.10,lw=0)
for kind,col,lab in [('none',GRAY,'sin autopista'),('rnl',BLUE,'hereda la autopista de RⁿL'),('other',ORANGE,'otra autopista')]:
    xs=[];ys=[]
    for r in E:
        k='none' if not r['hw'] else ('rnl' if r.get('src2') and r['src2'].count('L')==1 and r['src2'].endswith('L') else 'other')
        if k!=kind or r['t100']<0: continue
        xs.append((r['amin']+r['amax'])/2); ys.append(r['t100']/16384)
    a0.scatter(xs,ys,s=9,color=col,label=lab,lw=0)
for name,lab in [('dorado','dorado'),('plata','plata'),('bronce','bronce')]:
    al=ALPHAS[name]; a0.axvline(al,color=MUTED,lw=0.8,ls='--'); a0.text(al+0.003,330,lab,color=MUTED,fontsize=8,rotation=90,va='top')
a0.set_yscale('log'); a0.set_xlim(0,0.5); a0.set_ylim(10,350)
a0.set_xlabel('ángulo de la regla α (vueltas); franjas: α ∈ [2/(2n+3), 1/(n+1))'); a0.set_ylabel('tiempo para cubrir el toro 128×128 (en n²)')
a0.set_title('(a) Reglas = rotación por α, N = 60',loc='left',fontsize=10,color=INK)
a0.legend(frameon=False,fontsize=8,loc='lower left')
# (b) torus scaling
D=json.load(open('e4.json')); res=D['res']; ns=[32,64,128,256,512]; a1=ax[1]
for g,col,lab in [(D['fast'],BLUE,'con autopista temprana'),(D['cha'],ORANGE,'caóticas')]:
    med=[np.median([res[str(n)][w]['t90']/(n*n) for w in g if res[str(n)][w]['t90']>=0]) for n in ns]
    a1.plot(ns,med,'-o',color=col,lw=2,ms=5); a1.text(ns[-1]*1.08,med[-1],lab,color=INK,fontsize=8,va='center')
rw=[4/math.pi*math.log(n)**2 for n in ns]; a1.plot(ns,rw,'--',color=GRAY,lw=1.5); a1.text(ns[-1]*1.08,rw[-1],'caminata\naleatoria',color=MUTED,fontsize=8,va='center')
a1.set_xscale('log',base=2); a1.set_yscale('log'); a1.set_xlim(26,1500)
a1.set_xlabel('lado del toro n'); a1.set_ylabel('pasos para cubrir el 90% (en n², mediana)')
a1.set_title('(b) Cubrir un toro n×n',loc='left',fontsize=10,color=INK)
# (c) prefix explains coverage
E1=json.load(open('e1.json')); E2=json.load(open('e2.json'))
def series(ws,y,ks,rng):
    out=[];ctl=[]
    for k in ks:
        g=collections.defaultdict(list)
        for w,v in zip(ws,y): g[w[:k]].append(v)
        within=sum(((np.array(v)-np.mean(v))**2).sum() for v in g.values())/len(y); out.append(1-within/y.var())
        sizes=[len(v) for v in g.values()]; R=[]
        for rep in range(200):
            p=rng.permutation(y); i=0; wi=0
            for s in sizes: seg=p[i:i+s]; wi+=((seg-seg.mean())**2).sum(); i+=s
            R.append(1-wi/len(y)/y.var())
        ctl.append(np.percentile(R,99))
    return out,ctl
rng=np.random.default_rng(0); ks=[2,3,4,5,6,8,10]
d={}
for w,v in E1['toro'].items():
    if len(w)>=30 and v['t100']>=0 and not E1['plano'][w]['hw']: d[w]=math.log(v['t100'])
for N,rows in E2.items():
    for r in rows:
        if not r['hw'] and r['t100']>=0 and len(r['w'])>=30: d[r['w']]=math.log(r['t100'])
ws=list(d); y=np.array([d[w] for w in ws]); o1,c1=series(ws,y,ks,rng)
sh=[w for N,it in E1['R'].items() for c,w in it if c=='barajada' and E1['toro'][w]['t100']>=0 and not E1['plano'][w]['hw']]
y2=np.array([math.log(E1['toro'][w]['t100']) for w in sh]); o2,c2=series(sh,y2,ks,rng)
a2=ax[2]
a2.plot(ks,o1,'-o',color=BLUE,lw=2,ms=5); a2.text(10.3,o1[-1],'todas (N = 30–60)',fontsize=8,color=INK,va='center')
a2.plot(ks,o2,'-o',color=AQUA,lw=2,ms=5); a2.text(10.3,o2[-1],'mismas letras,\notro orden',fontsize=8,color=INK,va='center')
a2.plot(ks,c1,':',color=GRAY,lw=1.5); a2.plot(ks,c2,':',color=GRAY,lw=1.5); a2.text(10.3,max(c1[-1],c2[-1])-0.03,'azar (p99)',fontsize=8,color=MUTED,va='center')
a2.set_xlim(1.5,13.5); a2.set_ylim(0,1); a2.set_xlabel('primeras k letras de la regla'); a2.set_ylabel('varianza explicada del tiempo de cobertura')
a2.set_title('(c) Lo que importa es el prefijo',loc='left',fontsize=10,color=INK)
plt.tight_layout(); plt.savefig('hormiga_angulos.png',dpi=160)
print(o1,c1,o2,c2)
