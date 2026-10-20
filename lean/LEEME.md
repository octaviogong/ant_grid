# Formalización en Lean 4: autopistas de RⁿLᵐ desde el tablero en blanco

Verificado con Lean 4.37.0-pre (compilado desde el código fuente, commit 40b1e71, 19-oct-2026).
`lean-toolchain` fija la nightly más cercana (`nightly-2026-10-20`); el código solo usa Lean y su biblioteca
estándar (`Std.HashMap`), así que debería compilar con cualquier versión de esas fechas.
Sin Mathlib y sin `sorry`. Es la parte formal del artículo (en preparación).

## Teoremas finales (`Hormiga/Certificados.lean`)

```lean
-- Bueno n j : con m = 2j+1, la hormiga RⁿLᵐ desde el tablero en blanco entra, en un paso t1 ≤ 204·(n + m),
--             en una autopista con periodo 16(n + m) − 20 y alguna deriva d.
def Bueno (n j : Nat) : Prop :=
  ∃ t1, t1 ≤ 204 * (n + 2*j + 1) ∧
    ∃ d, EsAutopista (RL n (2*j+1)) (iter (RL n (2*j+1)) t1 blanco.toE) (16*(n+2*j+1) - 20) d

theorem ley_m5 (n j : Nat) : 2 ≤ j → 2*j ≤ n → ¬(n = 12 ∧ j = 6) → Bueno n j   -- m ≥ 5, n ≥ m − 1
theorem ley_m3 (n : Nat) : 3 ≤ n → Bueno n 1                                   -- m = 3, n ≥ 3

-- Familia RⁿL (espejo de LⁿR): periodo 16n + 4, inicio a más tardar en el paso 40·(n + 1).
theorem ley_RnL (n : Nat) (hn : 2 ≤ n) :
    ∃ t1, t1 ≤ 40 * (n + 1) ∧ ∃ d, EsAutopista (RL n 1) (iter (RL n 1) t1 blanco.toE) (16 * n + 4) d
```

`EsAutopista R s P d` significa: para todo q y todo i < P, el paso q·P + i está en la posición del
paso i trasladada q·d y con la misma dirección. Es decir, la trayectoria se repite para siempre.

Ejemplos concretos:
- `Ejemplos.lean`: `langton_autopista` (la hormiga de Langton, RL, entra en la autopista de periodo 104)
  y `excepcion_12_13` (R¹²L¹³ entra en otra autopista, de periodo 996 y deriva (6, −6)).
- `NoDiagonales.lean`: las 12 autopistas **no diagonales** del catálogo, desde el blanco (inicios de hasta
  1.6 millones de pasos), con el verificador rápido de `Rapido.lean`.

## Cómo compilarlo en tu computadora

1. Instala elan: https://lean-lang.org/install/
2. En esta carpeta: `lake build` (todo compila en alrededor de un minuto).
3. Para ver enunciados y axiomas: `lake env lean Hormiga/Verificacion.lean`.

Si tu versión de Lean es más vieja o más nueva, puede pedir cambios menores de nombres de lemas.

## Estructura

| Archivo | Líneas | Contenido | Confianza |
|---|---|---|---|
| `Basico.lean` | 201 | Modelo de la hormiga (cualquier regla), **lema de repetición** → autopista, duplicación del periodo. | núcleo de Lean |
| `Concreto.lean` | 157 | Verificador concreto con listas, demostrado correcto. | núcleo de Lean |
| `Ciclo.lean` | 164 | **Lema de ciclos**: repetir una vuelta r veces = sumar r·Δ a los colores. | núcleo de Lean |
| `Simbolico.lean` | 680 | Verificador **paramétrico** (colores = formas afines en s, t) y su corrección `verificaS_ok`. | núcleo de Lean |
| `Certificados.lean` | 1230 | GENERADO por `prueba/gen_lean.py`: 42 certificados, árbol de 77 casos y los teoremas finales. | ver abajo |
| `Ejemplos.lean` | 19 | Langton (104) y la excepción (996). | `native_decide` |
| `Rapido.lean` | 115 | Verificador concreto con tabla hash (`Std.HashMap`), demostrado correcto: O(1) por paso. | núcleo de Lean |
| `NoDiagonales.lean` | 72 | Las 12 autopistas no diagonales desde el blanco. | `native_decide` |
| `Verificacion.lean` | 17 | Imprime los enunciados y los axiomas de los teoremas finales. | — |

El árbol de casos tiene 77 nodos y 43 hojas: 42 piezas con certificado (32 para m ≥ 5, 7 para m = 3,
3 para m = 1) y el punto aislado (12, 13), que es una excepción real.

## Qué hay que confiar

- **Teoremas generales** (`verificaS_ok`, `autopista_de_repeticion`, lema de ciclos): solo los axiomas
  estándar de Lean (`propext`, `Classical.choice`, `Quot.sound`).
- **Certificados**: los 42 se evalúan con `native_decide`, es decir, con el compilador de Lean
  (un axioma `cert…native_decide` por certificado). Se intentó la revisión solo con el núcleo
  (`decide +kernel`, con `python3 gen_lean.py "decide +kernel"`): funciona en los certificados chicos
  (por ejemplo cert2, en 9 s), pero los grandes agotan 7 GB de memoria. Con más memoria, o con un
  verificador optimizado para el núcleo, se eliminaría también esta dependencia.
- **Python** no forma parte de la prueba: solo encontró los certificados y el árbol de casos.
  Si un certificado fuera incorrecto, Lean lo rechazaría.

Para comprobar los axiomas: `#print axioms Hormiga.ley_m5` (archivo `Verificacion.lean`).
