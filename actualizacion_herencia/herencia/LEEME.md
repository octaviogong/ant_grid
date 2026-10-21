# Teorema de herencia por prefijo

## Enunciado

Sea m = 2j + 1 impar, n ≥ m (o bien m = 1 y n ≥ 2), N = n + m y

  K = N + n + 1 = 2n + m + 1.

**Teorema.** Toda regla w, de cualquier longitud, cuyas primeras K letras sean

  RⁿLᵐRⁿL

recorre desde el tablero en blanco **exactamente la misma trayectoria** (posición y dirección en cada paso)
que RⁿLᵐ. En particular entra en la autopista de RⁿLᵐ en el mismo paso, a más tardar en el paso
204(n + m) (40(n + 1) si m = 1), con periodo 16(n + m) − 20 (16n + 4 si m = 1).

Así, los teoremas del artículo pasan de una regla por cada par (n, m) a todas las reglas que empiezan con
RⁿLᵐRⁿL, de todas las longitudes. Entre las palabras de longitud dada que empiezan con R, una fracción
2^−(2n+m) empieza con ese prefijo.

En Lean (`lean/Hormiga/HerenciaTeorema.lean`): `herencia`, `herencia_RnL` y sus versiones con palabras
`herencia_palabra`, `herencia_palabra_RnL`. Sin `sorry`. Los axiomas son los estándar más uno
de `native_decide` por cada uno de los 19 certificados, como en el artículo.

## Idea de la prueba

1. **Sólo se lee un prefijo.** Desde el blanco, una casilla visitada k veces ha leído los colores 0, 1, …, k − 1.
   Si una hormiga nunca lee un color ≥ K, cualquier regla que coincida con ella en los colores < K hace lo mismo
   (`acople_tray` en `Herencia.lean`).
2. **Regla levantada.** U(n, m) tiene 3N colores y la letra de c es la de c mod N en RⁿLᵐ. Tiene la misma
   trayectoria que RⁿLᵐ (`proy_tray`), pero sus colores cuentan visitas, porque nunca llegan a 3N.
3. **Cota de visitas para toda la familia.** `SimbolicoU.lean` adapta el verificador simbólico del artículo a U.
   Clasifica cada color leído en [0, n−1] (R), [n, N−1] (L), [N, N+n−1] (R) o {N+n} (L), y falla si puede
   pasar de N + n. Su corrección (`verificaU_ok`) da a la vez la autopista y la cota de lectura para todo
   tiempo. Antes del cierre la cota sale del invariante, que ahora incluye los colores leídos en las vueltas
   aceleradas (`ciclo_lee`). Después del cierre sale de que el color leído también es periódico (`lee_periodica`).
4. **Los mismos certificados.** Las 19 piezas del árbol de casos con n ≥ 2j + 1 se re-verifican con U usando
   *los mismos* segmentos del artículo (`HerenciaCert.lean`, generado por `gen_herencia.py`). Las piezas de la
   línea n = 2j (n = m − 1) no cumplen la cota: ahí la casilla más visitada llega más lejos (por ejemplo,
   K = 25, 36, 52 y 77 para (4,5), (6,7), (8,9) y (10,11)).

## Qué está demostrado y qué no

- **Demostrado en Lean:** el teorema para m impar ≥ 3 con n ≥ m, y para m = 1 con n ≥ 2.
- **Observado, no demostrado:** que K es justo. Si se cambia la letra K − 1 (la última L del prefijo), ninguna
  de 320 reglas al azar repite la autopista (`exploracion/angulos`).
- **Fuera del teorema:** la línea n = m − 1, donde K es mayor y depende de la pieza.

## Archivos

- `replica_u.py`: réplica en Python del verificador U, para probar los certificados antes de Lean.
- `gen_simbolicoU.py`: genera `lean/Hormiga/SimbolicoU.lean` a partir de `Simbolico.lean`.
- `gen_herencia.py`: genera `lean/Hormiga/HerenciaCert.lean` a partir de `prueba/arbol_B.json`.

Para regenerar y compilar:
```bash
python3 herencia/gen_simbolicoU.py && python3 herencia/gen_herencia.py
cd lean && lake build
```
