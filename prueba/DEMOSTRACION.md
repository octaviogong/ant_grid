# Teorema: periodo de la autopista de RⁿLᵐ (demostración asistida por computadora)

## Enunciado

Sea la hormiga generalizada RⁿLᵐ: en una casilla de estado k gira a la derecha si k < n y a la
izquierda si n ≤ k < n + m; después el estado pasa a k + 1 (mod n + m) y avanza una casilla.

**Teorema.** Sea m impar, m = 2j + 1 ≥ 3, y sea n ≥ m − 1 (con n ≥ 3 cuando m = 3).
Excepto en el caso (n, m) = (12, 13), la hormiga que parte del tablero en blanco entra, **a más tardar en el paso 204·(n + m)**, en una
autopista con deriva diagonal (±2, ±2), y **16(n + m) − 20 es un periodo de esa autopista**.

- Cuando n = 3j o (n, m) = (4, 5), la autopista se repite ya a la mitad, (16(n + m) − 20)/2, con deriva
  (±1, ±1). En los demás casos, 16(n + m) − 20 fue el periodo mínimo en los 575 casos concretos revisados;
  la minimalidad general no está demostrada, solo que es un periodo.
- La cota 204·(n + m) del transitorio está verificada en Lean; el peor caso es R¹⁴L¹⁵, que empieza a más tardar en el paso 5 888.
- La excepción (12, 13) es real: desde el blanco entra en otra autopista, de periodo 996 y
  deriva (6, −6), con certificado exacto.

**Parte A (semilla).** Para todo m impar ≥ 3 y n ≥ m − 1, la configuración finita H(n, m) de 14 casillas
inicia una autopista con el mismo periodo. Esto incluye (12, 13): la autopista existe, pero desde el blanco
la hormiga no llega a ella.

```
H(n, m), relativo a la hormiga (que está en (0,0) mirando al sur); j = (m−1)/2:
(−2,4)=j      (−1,4)=j        (0,4)=j
(−2,3)=j      (−1,3)=n+2j
(−2,2)=2j−1   (−1,2)=j−1      (0,2)=n
(−2,1)=2j−1   (−1,1)=n+2j−1   (0,1)=n−j+1
              (−1,0)=n−1      (0,0)=n−j−2
              (−1,−1)=j−1
```

Relación con lo publicado: para m = 1 (familia RⁿL, espejo de LⁿR) el teorema `ley_RnL` (Lean) da periodo
16n + 4 para n ≥ 2 desde el blanco (mínimo 18 para RRL). Gajardo, Lutfalla y Rao (2025) prueban, desde semillas,
periodos 16k + 2 y 32k + 4 para L²ᵏR, y anuncian sin prueba 32k + 20 para L²ᵏ⁺¹R; nuestro teorema cubre ese caso
desde el blanco. Para m ≥ 3 la fórmula no aparece en la literatura que revisamos.

## Lema de repetición (la pieza que convierte "simulado" en "demostrado")

Sean t1 < t2 = t1 + P, d = pos(t2) − pos(t1) ≠ 0, misma dirección en t1 y t2, V = casillas visitadas
en [t1, t2), φ(x) = ⟨x, d⟩ y S = {x : φ(x) ≥ mín_{c∈V} φ(c)}.
Si config(t2)[x + d] = config(t1)[x] para toda x en S, la hormiga repite ese periodo para siempre.

*Demostración.* (i) Como V ⊂ S, en [t2, t2 + P) la hormiga lee en c + d lo mismo que leyó en c, paso a
paso, así que repite giros y cambios. (ii) Para x en S, x + d también está en S, así que
config(t2+P)[x+2d] = config(t2)[x+2d] + Δ(x+d) = config(t1)[x+d] + Δ(x+d) = config(t2)[x+d],
donde Δ es el cambio de cada casilla en el primer periodo. Es la misma hipótesis para (t2, t2+P) en
el semiplano S + d ⊂ S, y se itera. ∎

Nota: una primera versión pedía la igualdad solo en V. Eso **no basta**, porque la hormiga puede ir
recorriendo una estructura finita construida antes. La versión corregida es la que se usa en todo.

## Método

1. **Ejecución simbólica.** n y j son variables. Cada estado de casilla es una forma afín en dos
   parámetros enteros s, t ≥ 0. Cada decisión (¿estado < n?, ¿llega a n + m?) se resuelve para toda
   la región a la vez: a + b·s + c·t ≥ 0 para todo s, t ≥ 0 si y solo si a, b, c ≥ 0.
2. **Aceleración.** Cuando la hormiga vuelve a la misma (posición, dirección), el tramo es un ciclo.
   Se repite r = mín_k ⌊holgura_k / Δ_k⌋ veces de golpe, con r simbólico. Así las vueltas de longitud
   ~4n cuestan una sola operación y la ejecución es finita para todos los n y m a la vez.
3. **División de casos.** Si una decisión depende del punto, la región se parte en piezas que la cubren
   exactamente (umbrales, franjas finitas y residuos). Aparecen fronteras reales, como n = 3j o
   2n = 5j, donde el orden interno de los pasos cambia aunque el periodo no.
4. **Cierre.** En cada pieza se busca un par de eventos que cumpla el lema, de forma simbólica. El
   periodo resultante se compara como forma afín con 16(n + m) − 20.

## Piezas de la demostración desde el blanco (m ≥ 5; s, t ≥ 0 son los parámetros de cada pieza)

| n | j (m = 2j+1) | periodo demostrado | deriva | empieza a más tardar en | estado |
|---|---|---|---|---|---|
| 4 | 2 | 62 | (-1, 1) | 522 | mitad de 16(n+m)−20 |
| 6 | 3 | 188 | (-2, 2) | 1565 | 16(n+m)−20 |
| 8 | 4 | 252 | (-2, 2) | 2658 | 16(n+m)−20 |
| 10 | 5 | 316 | (-2, -2) | 2736 | 16(n+m)−20 |
| 12 | 6 | — | — | — | excepción (ver texto) |
| 14 | 7 | 444 | (2, -2) | 5888 | 16(n+m)−20 |
| 16 | 8 | 508 | (-2, -2) | 3692 | 16(n+m)−20 |
| 18 | 9 | 572 | (-2, -2) | 4132 | 16(n+m)−20 |
| 20 | 10 | 636 | (-2, -2) | 4624 | 16(n+m)−20 |
| 22 | 11 | 700 | (-2, -2) | 5060 | 16(n+m)−20 |
| 24 | 12 | 764 | (-2, -2) | 5420 | 16(n+m)−20 |
| 26 | 13 | 828 | (-2, -2) | 5796 | 16(n+m)−20 |
| 28 | 14 | 892 | (-2, -2) | 6172 | 16(n+m)−20 |
| 34 | 17 | 1084 | (-2, -2) | 7448 | 16(n+m)−20 |
| 40 | 20 | 1276 | (-2, -2) | 8772 | 16(n+m)−20 |
| 6t+46 | 3t+23 | 192t+1468 | (-2, -2) | 1308t+10080 | 16(n+m)−20 |
| 30 | 15 | 956 | (-2, -2) | 6548 | 16(n+m)−20 |
| 36 | 18 | 1148 | (-2, -2) | 7900 | 16(n+m)−20 |
| 42 | 21 | 1340 | (-2, -2) | 9208 | 16(n+m)−20 |
| 6t+48 | 3t+24 | 192t+1532 | (-2, -2) | 1308t+10516 | 16(n+m)−20 |
| 32 | 16 | 1020 | (-2, -2) | 6996 | 16(n+m)−20 |
| 38 | 19 | 1212 | (-2, -2) | 8336 | 16(n+m)−20 |
| 44 | 22 | 1404 | (-2, -2) | 9644 | 16(n+m)−20 |
| 6t+50 | 3t+25 | 192t+1596 | (-2, -2) | 1308t+10952 | 16(n+m)−20 |
| 3s+6 | 1s+2 | 40s+78 | (-1, 1) | 104s+209 | mitad de 16(n+m)−20 |
| 3s+1t+7 | 1s+2 | 80s+16t+172 | (-2, 2) | 104s+16t+225 | 16(n+m)−20 |
| 5 | 2 | 140 | (-2, 2) | 189 | 16(n+m)−20 |
| 5s+10 | 2s+4 | 144s+284 | (-2, 2) | 192s+385 | 16(n+m)−20 |
| 5s+3t+8 | 2s+1t+3 | 144s+80t+220 | (-2, 2) | 192s+104t+297 | 16(n+m)−20 |
| 6t+7 | 3t+3 | 192t+204 | (-2, 2) | 264t+281 | 16(n+m)−20 |
| 6t+9 | 3t+4 | 192t+268 | (-2, 2) | 264t+369 | 16(n+m)−20 |
| 6t+11 | 3t+5 | 192t+332 | (-2, 2) | 264t+457 | 16(n+m)−20 |
| 5s+2t+12 | 2s+1t+5 | 144s+64t+348 | (-2, 2) | 192s+88t+473 | 16(n+m)−20 |

## Piezas para m = 3

| n | j (m = 2j+1) | periodo demostrado | deriva | empieza a más tardar en | estado |
|---|---|---|---|---|---|
| 3 | 1 | 38 | (-1, 1) | 99 | mitad de 16(n+m)−20 |
| 6s+9 | 1 | 96s+172 | (-2, 2) | 96s+195 | 16(n+m)−20 |
| 6s+5 | 1 | 96s+108 | (-2, 2) | 96s+131 | 16(n+m)−20 |
| 6s+7 | 1 | 96s+140 | (-2, 2) | 96s+163 | 16(n+m)−20 |
| 6s+4 | 1 | 96s+92 | (-2, 2) | 96s+115 | 16(n+m)−20 |
| 6s+6 | 1 | 96s+124 | (-2, 2) | 96s+147 | 16(n+m)−20 |
| 6s+8 | 1 | 96s+156 | (-2, 2) | 96s+179 | 16(n+m)−20 |

## Verificaciones independientes

- **Cobertura.** Las piezas cubren la región sin huecos ni traslapes, por construcción y revisado
  en 23,400 puntos (j de 2 a 79, n de 2j a 2j + 299).
- **Desde el blanco.** 516 casos concretos (m de 5 a 25, n hasta 60), simulados con enteros y el lema
  corregido sin usar el motor simbólico, coinciden uno por uno con el periodo simbólico. Ninguno difiere.
- **Semilla.** 1,470 puntos verificados de forma concreta (Parte A). Ningún fallo.
- **Control.** Con m = 1 el motor reproduce el teorema publicado de Gajardo, Lutfalla y Rao.

## Límites honestos

- Es una demostración **asistida por computadora**, pero ya **no depende de Python**: los certificados
  que encuentra el motor se revisan en Lean 4 con un verificador demostrado correcto (`../lean`).
  Lo único que se confía más allá del núcleo de Lean es `native_decide` (un axioma por certificado, 42 en total).
- La minimalidad del periodo no está demostrada en general; se comprobó en los 575 pares con m impar de 3 a 25
  y m − 1 ≤ n ≤ 60: es 16(n + m) − 20, o la mitad exactamente cuando n = 3j o (n, m) = (4, 5), salvo (12, 13).
- Para m par no hay enunciado: en la malla no aparece ninguna autopista con n ≥ m − 1.

## Cómo reproducirlo

```bash
python3 parteA_total.py            # Parte A, m >= 5 (17 piezas)
python3 partes_m3_y_B.py A3        # Parte A, m = 3
python3 partes_m3_y_B.py B3        # desde el blanco, m = 3
python3 partes_m3_y_B.py B         # desde el blanco, m >= 5 (33 piezas)
python3 cobertura.py parteB.json   # cobertura exacta
python3 verifica_parteA.py         # verificación concreta de la Parte A
python3 certificado.py 60 3 25 2 malla_impar2.json   # malla concreta con el lema corregido
```

## Por qué 16(n + m) − 20 (anatomía de un periodo)

La versión completa está en la sección 4 del artículo. Resumen, para j ≥ 2 y n ≥ 3j + 1:

```
S1 4(n−j) | A 16j | 1 | S2 4(n−3j) | B 8j | 1 | S3 4(n−3j) | C 8(j−1) | 4 |
S4 4(n−j) | A 16j | 1 | B 8j | 1 | C 8(j−1) | 4            = 16n + 32j − 4 = 16(n + m) − 20
```

- **Espirales** (S1–S4): cuatro giros a la derecha alrededor de un bloque de 2×2; cada vuelta sube el bloque
  en 1 hasta que una casilla llega a n (lema de espirales: n − máx vueltas).
- **Escaleras** A = LRRRL·LRRRL·LRRRL·R, B = LRRRLRRR, C = RRLRRRLR: lazos con **pivotes** (casillas que se leen
  dos veces por vuelta girando a la izquierda). Un pivote entra en n y sube 2 por vuelta; como m = 2j + 1 es impar,
  permite exactamente j vueltas, queda en N − 1 y al siguiente paso da la vuelta a 0. Ese 0 es la cuarta casilla
  del siguiente bloque de espiral. C la detiene un contador de giro a la derecha que entra en n − j + 1 (j − 1 vueltas).
- **Libro de niveles** (tabla 3 del artículo): cada estado de entrada es una suma de conteos completos de fases
  (j por escalera, 2j por pivote, n − j o n − 3j por espiral, 1 por conector). El nivel j viene de una escalera,
  el 3j de tres, y el 0 de un pivote que dio la vuelta completa a los N estados.
- **La frontera n = 3j**: S2 y S3 tienen cero vueltas, las dos mitades del periodo coinciden y el periodo mínimo
  es la mitad.
- Para 2j ≤ n ≤ 3j − 1 hay otras piezas, con lazos de 20 y 12 pasos; el total sigue siendo 16n + 32j − 4.

`fases.py alto|bajo` reproduce la descomposición a partir del certificado.

## Toros: por qué aparece la antiperiodicidad

**Lema.** Sea σ = (invertir todos los colores) ∘ (reflejar el toro, x ↦ −x). Entonces σ conmuta con la
hormiga RL: con el color invertido la hormiga gira al lado contrario, y la reflexión lo corrige. Si la
órbita del tablero blanco pasa por un tablero totalmente negro (en cualquier posición y dirección), el
estado negro es la imagen por σ, compuesta con una simetría del toro, del estado blanco. Por lo tanto,
desde ese momento la hormiga lee exactamente los colores complementarios: la sucesión es antiperiódica.

**Lo que queda abierto.** ¿Qué toros pasan por el tablero negro? En los datos (N, M ≤ 8) son
exactamente 1×1, 1×2, 2×2, 4×4 y 8×8. Conjetura: los de lado 2ᵏ × 2ᵏ (y 1×2).
