# Ángulos, Fibonacci y herencia por prefijo (21 oct 2026)

Exploración de la idea "la regla como ángulo" (filotaxis / ángulo dorado) para hormigas generalizadas.

## Programas
- `plano.c` — hormiga desde el tablero blanco en el plano; detecta autopista (P, desplazamiento, inicio)
  con el criterio del catálogo y mide K = máximo de visitas a una misma casilla.
- `toro.c` — tiempo para cubrir el 50/90/100 % de un toro n×n.
- `palabras.py` — reglas como codificación de una rotación por α (la letra c es L cuando el giro c+1→c+2 completa vuelta);
  α = 1/φ² da la palabra de Fibonacci RLRRLRLRRLRR…
- `correr.py` — corre los dos programas en paralelo.
- `herencia.py` — herencia por prefijo en el catálogo (2–12 estados).
- `e1.py` / `e1_an.py` — prueba confirmatoria, N = 13..60: Fibonacci vs plata, bronce, α al azar, barajadas, bloques.
- `e2.py` — barrido del ángulo α (N = 30 y 60).
- `e3.py` — dorado con otras fases; números nobles vs colas de 2 y de 4.
- `e4.py` — escalamiento del tiempo de cobertura del toro (n = 32..512).
- `figura.py` — figura `hormiga_angulos.png`.

## Resultados principales
1. **Herencia por prefijo (lema).** Si la trayectoria de u desde el blanco nunca visita una casilla más de K_u veces,
   toda regla w con w[c mod N] = u[c mod q] para c < K_u tiene exactamente la misma trayectoria.
   En el catálogo: 169 de 459 autopistas (37 %) son heredadas así, sin ninguna excepción.
2. **Presupuesto de visitas de la familia del artículo.** K(RⁿL) = 2n+2 (n = 2..60) y K(RⁿLᵐ) = 2n+m+1
   para m impar y n ≥ m (m = 3..11). En la línea n = m−1, K es mayor (25, 36, 52, 77).
   Consecuencia observada: toda regla que empieza con RⁿLᵐRⁿL hace la autopista de RⁿLᵐ con el mismo
   periodo e inicio (320/320 al azar; si se cambia la última letra del prefijo: 0/320).
3. **Lenguas en α.** Las codificaciones con α ∈ [2/(2n+3), 1/(n+1)) heredan la autopista de RⁿL
   (222 palabras, 0 excepciones; cubren el 36 % de (0, 1/2)). Con N = 60, el 81 % de las autopistas son heredadas.
4. **El ángulo dorado como tal no importa.** Fibonacci, N = 13..60: 0/45 autopistas; plata 0/44;
   bronce 45/45 (exactamente la autopista de RRL). Con otra fase, el dorado no es más rápido y 2/13 heredan RRL.
   Nobles vs colas de 2 o de 4: sin diferencia. El prefijo de k letras explica el 64 % (k = 6) y el 83 % (k = 10)
   de la varianza del tiempo de cobertura (control al azar, percentil 99: 5 % y 26 %).
5. **Cubrir un toro.** Mediana de t90/n² de n = 32 a 512: reglas con autopista temprana 10 → 22;
   caóticas 13 → 158; caminata aleatoria 15 → 50. En el plano, las caóticas visitan ~t^0.69 casillas
   (IQR 0.66–0.71), lo que da una cobertura ~n^2.9.

## Cómo reproducir
```bash
gcc -O2 -o plano plano.c && gcc -O2 -o toro toro.c
python3 herencia.py          # K_catalogo.json (presupuesto de visitas de las autopistas del catálogo)
python3 e1.py && python3 e1_an.py
python3 e2.py && python3 e3.py && python3 e4.py
python3 figura.py            # hormiga_angulos.png
```
`pendientes.json` (catálogo de autopistas, 2–12 estados) se lee de la carpeta de arriba.
El teorema que salió de aquí está demostrado en Lean: `lean/Hormiga/HerenciaTeorema.lean` (ver `herencia/LEEME.md`).
