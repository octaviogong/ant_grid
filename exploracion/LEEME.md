# Hormiga de Langton como operador: ¿lee la aritmética de su entrada?

Exploración inicial (antes del artículo): la hormiga como operador sobre el tablero, toros, dimensiones
superiores y el catálogo de reglas de 2 a 12 colores (`pendientes.py` → `pendientes.json`), que usa
`../semillas`.

## Cómo correrlo

```bash
gcc -O3 -shared -fPIC -o libant.so ant_core.c
gcc -O3 -shared -fPIC -o librule.so ant_rule.c
python3 experimentos.py   # 1,365 entradas + 40 sustitutos c/u  -> resultados.csv, resumen.json, salida.txt
python3 seguimiento.py    # controles estrictos                  -> seguimiento.txt
python3 replica.py        # réplica fuera de muestra             -> replica.txt
python3 reglas.py         # 502 operadores sobre tablero blanco  -> reglas.json, reglas.txt
```

Requiere Python 3 con numpy y scipy. Todo corre en menos de un minuto.

## Archivos

| Archivo | Qué hace |
|---|---|
| `ant_core.c` / `antlib.py` | Hormiga RL en C. Detecta y certifica la autopista: la hormiga sale de la zona del caos sin romper el periodo 104. También corre el pasado. |
| `codif.py` | Codificaciones de entradas: cociente, tabla de residuos, par de vectores, filas, Pascal mod 2, series sobre F2 y bits de irracionales (aritmética entera exacta). |
| `experimentos.py` | Tres familias de entradas: primos, series de potencias y factoriales. |
| `seguimiento.py` | Sustitutos con extremos y bordes fijos, nulos aritméticos, raíces primitivas, futuro contra pasado e invariantes exactos. |
| `replica.py` | Prueba de permutación por bloques y tres réplicas con primos nuevos. |
| `ant_rule.c` / `reglas.py` | Turmitas de 2 a 9 colores: el periodo de la autopista según la regla. |
| `familias.py` | Familias RⁿL, RⁿLL, RⁿLLL y RⁿL⁵ hasta n=16. |
| `prediccion.py` | Primera ley propuesta (cuadrática en m). Falló: 0/28. |
| `prediccion2.py` | Ley corregida P = 16·(n+m) − 20, probada con m=11 y 13, que no se usaron para ajustarla: 27/29. |

## Medida principal

T es el número de pasos de caos antes de la autopista. Para cada entrada se calcula
z = (log T − media) / desviación, comparando contra 40 sustitutos. Cada sustituto tiene
las mismas casillas negras barajadas dentro de las mismas ranuras: conserva la densidad
y la geometría, pero pierde la aritmética.

Si la hormiga leyera la aritmética de la entrada, z se alejaría de 0 de forma sistemática.

## Decodificar el tablero como fracción

Si c_t es el color que pisa la hormiga en el paso t, se define x = 0.c₁c₂c₃… en base 2.
La conjetura de la autopista equivale a que x sea racional para todo tablero finito.

| Archivo | Qué hace |
|---|---|
| `decodificar.py` | Fracción exacta para el tablero blanco, 2 diagonales y 3 diagonales. Denominador = 2^T · (2¹⁰⁴−1)/5. |
| `factor.py` | Factoriza el denominador común (Miller–Rabin y Pollard rho). |
| `toro.c` | Periodo exacto en tableros finitos N×M con bordes que se enrollan. |
| `toro_frac.py` | Fracción decodificada en toros pequeños: 1×2 → 1/5, 2×2 → 1/17. |
| `toro_anti.py` / `toro_anti.c` | Antiperiodicidad (la segunda mitad es el complemento de la primera). Aparece en 1×1, 1×2, 2×2, 4×4 y 8×8. |

```bash
gcc -O3 -o toro toro.c && ./toro 5 5 3000000000
gcc -O3 -o toro_anti toro_anti.c && ./toro_anti 8 8 200000000
```

## Dimensiones superiores (3D y 4D)

La hormiga lleva un marco (adelante, derecha, arriba, w). Cada color indica hacia qué eje del
cuerpo gira 90°: R/L (derecha/izquierda), U/D (arriba/abajo) y W/X (cuarto eje).

| Archivo | Qué hace |
|---|---|
| `antnd.c` / `antnd.py` | Hormiga en d dimensiones con tablero disperso (hash). Detecta autopistas y ciclos, y canoniza reglas por simetría. |
| `dimensiones.py` | 240 reglas distintas: 3D de 2 a 5 colores y 4D de 2 a 4. 20 millones de pasos cada una. |
| `verifica3d.py` | Verificación independiente en Python: la hormiga 3D de 2 colores vuelve al vacío cada 32 pasos. |
| `ciclo_nd.c` | Pasos exactos hasta volver al vacío (ciclos de 4D: entre 8,400 y 415,536). |
| `robustez_nd.py` | 30 tableros iniciales al azar por regla: ¿mismo patrón que desde el vacío? |
| `verifica_nodiag.py` | Re-verificación de las autopistas no diagonales del plano con 20 millones de pasos. |
