"""Reglas como codificaciones de una rotación: la letra c es L cuando el giro c+1 -> c+2 de ángulo alpha
(en vueltas) completa una vuelta. alpha = 1/phi^2 da la palabra de Fibonacci (ángulo dorado 137.5 grados)."""
import math, random
from fractions import Fraction
PHI=(1+5**0.5)/2
ALPHAS={'dorado':(3-5**0.5)/2, 'plata':2**0.5-1, 'bronce':(13**0.5-3)/2}
def rot(alpha,N,rho=0.0):
    return ''.join('L' if math.floor((c+2)*alpha+rho)-math.floor((c+1)*alpha+rho) else 'R' for c in range(N))
def primitive(w):
    N=len(w); return all(w != w[d:]+w[:d] for d in range(1,N) if N%d==0)
def imbalance(w):
    N=len(w); ww=w+w; best=0
    for l in range(1,N):
        c=[ww[i:i+l].count('R') for i in range(N)]; best=max(best,max(c)-min(c))
    return best
