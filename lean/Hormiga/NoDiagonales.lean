/-
  Las 12 autopistas NO diagonales del catálogo (reglas de 2 a 12 colores), desde el tablero en blanco.
  Cada una se comprueba con el verificador rápido (Rapido.lean) y el lema del semiplano.
-/
import Hormiga.Rapido

namespace Hormiga

/-- Regla dada por su palabra: la letra c dice si el color c gira a la derecha (R) o a la izquierda (L). -/
def regla (w : String) : Regla := ⟨w.length, fun c => decide (w.toList.getD c 'L' = 'R')⟩

/-- RLRLRLLRLR: periodo 138, deriva (-3, -1), a partir del paso 1432. -/
theorem nd_RLRLRLLRLR :
    EsAutopista (regla "RLRLRLLRLR") (iter (regla "RLRLRLLRLR") 1432 blanco.toE) 138 ⟨-3, -1⟩ :=
  autopista_desde_blancoH _ 1432 138 ⟨-3, -1⟩ 34 (by native_decide)

/-- RLRLRLLLRRL: periodo 490, deriva (-3, 5), a partir del paso 504099. -/
theorem nd_RLRLRLLLRRL :
    EsAutopista (regla "RLRLRLLLRRL") (iter (regla "RLRLRLLLRRL") 504099 blanco.toE) 490 ⟨-3, 5⟩ :=
  autopista_desde_blancoH _ 504099 490 ⟨-3, 5⟩ 532 (by native_decide)

/-- RRLLRLLRLRL: periodo 108, deriva (0, 2), a partir del paso 1640238. -/
theorem nd_RRLLRLLRLRL :
    EsAutopista (regla "RRLLRLLRLRL") (iter (regla "RRLLRLLRLRL") 1640238 blanco.toE) 108 ⟨0, 2⟩ :=
  autopista_desde_blancoH _ 1640238 108 ⟨0, 2⟩ 158 (by native_decide)

/-- RLRLLRLLLRLL: periodo 210, deriva (-1, 3), a partir del paso 1778. -/
theorem nd_RLRLLRLLLRLL :
    EsAutopista (regla "RLRLLRLLLRLL") (iter (regla "RLRLLRLLLRLL") 1778 blanco.toE) 210 ⟨-1, 3⟩ :=
  autopista_desde_blancoH _ 1778 210 ⟨-1, 3⟩ 41 (by native_decide)

/-- RLRLRLLRLRLR: periodo 146, deriva (1, -3), a partir del paso 22096. -/
theorem nd_RLRLRLLRLRLR :
    EsAutopista (regla "RLRLRLLRLRLR") (iter (regla "RLRLRLLRLRLR") 22096 blanco.toE) 146 ⟨1, -3⟩ :=
  autopista_desde_blancoH _ 22096 146 ⟨1, -3⟩ 91 (by native_decide)

/-- RLRLRLLRLRRL: periodo 138, deriva (-3, -1), a partir del paso 1432. -/
theorem nd_RLRLRLLRLRRL :
    EsAutopista (regla "RLRLRLLRLRRL") (iter (regla "RLRLRLLRLRRL") 1432 blanco.toE) 138 ⟨-3, -1⟩ :=
  autopista_desde_blancoH _ 1432 138 ⟨-3, -1⟩ 34 (by native_decide)

/-- RLRLRLLRRRLL: periodo 484, deriva (8, 0), a partir del paso 6441. -/
theorem nd_RLRLRLLRRRLL :
    EsAutopista (regla "RLRLRLLRRRLL") (iter (regla "RLRLRLLRRRLL") 6441 blanco.toE) 484 ⟨8, 0⟩ :=
  autopista_desde_blancoH _ 6441 484 ⟨8, 0⟩ 200 (by native_decide)

/-- RLRRLLRLLLLL: periodo 732, deriva (6, -2), a partir del paso 861201. -/
theorem nd_RLRRLLRLLLLL :
    EsAutopista (regla "RLRRLLRLLLLL") (iter (regla "RLRRLLRLLLLL") 861201 blanco.toE) 732 ⟨6, -2⟩ :=
  autopista_desde_blancoH _ 861201 732 ⟨6, -2⟩ 682 (by native_decide)

/-- RLRRLLRLRLRR: periodo 686, deriva (-5, -7), a partir del paso 556044. -/
theorem nd_RLRRLLRLRLRR :
    EsAutopista (regla "RLRRLLRLRLRR") (iter (regla "RLRRLLRLRLRR") 556044 blanco.toE) 686 ⟨-5, -7⟩ :=
  autopista_desde_blancoH _ 556044 686 ⟨-5, -7⟩ 724 (by native_decide)

/-- RLRRLRLRLRRR: periodo 1062, deriva (-3, 11), a partir del paso 49952. -/
theorem nd_RLRRLRLRLRRR :
    EsAutopista (regla "RLRRLRLRLRRR") (iter (regla "RLRRLRLRLRRR") 49952 blanco.toE) 1062 ⟨-3, 11⟩ :=
  autopista_desde_blancoH _ 49952 1062 ⟨-3, 11⟩ 434 (by native_decide)

/-- RRLLLRLRLRRL: periodo 1968, deriva (16, 0), a partir del paso 31858. -/
theorem nd_RRLLLRLRLRRL :
    EsAutopista (regla "RRLLLRLRLRRL") (iter (regla "RRLLLRLRLRRL") 31858 blanco.toE) 1968 ⟨16, 0⟩ :=
  autopista_desde_blancoH _ 31858 1968 ⟨16, 0⟩ 832 (by native_decide)

/-- RRLLLRRRLRRR: periodo 244, deriva (2, 0), a partir del paso 1164796. -/
theorem nd_RRLLLRRRLRRR :
    EsAutopista (regla "RRLLLRRRLRRR") (iter (regla "RRLLLRRRLRRR") 1164796 blanco.toE) 244 ⟨2, 0⟩ :=
  autopista_desde_blancoH _ 1164796 244 ⟨2, 0⟩ 136 (by native_decide)

end Hormiga
