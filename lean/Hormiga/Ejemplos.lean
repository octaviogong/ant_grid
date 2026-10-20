/-
  Ejemplos concretos verificados con el verificador concreto (Concreto.lean).
-/
import Hormiga.Concreto

namespace Hormiga

/-- La hormiga de Langton clásica (RL) entra, desde el blanco, en la autopista de periodo 104
    con deriva (-2, -2), a más tardar en el paso 10496. -/
theorem langton_autopista :
    EsAutopista (RL 1 1) (iter (RL 1 1) 10496 blanco.toE) 104 ⟨-2, -2⟩ :=
  autopista_desde_blanco 1 1 10496 104 ⟨-2, -2⟩ 48 (by native_decide)

/-- La excepción: R¹²L¹³ desde el blanco entra en OTRA autopista, de periodo 996 y deriva (6, -6). -/
theorem excepcion_12_13 :
    EsAutopista (RL 12 13) (iter (RL 12 13) 13436 blanco.toE) 996 ⟨6, -6⟩ :=
  autopista_desde_blanco 12 13 13436 996 ⟨6, -6⟩ 222 (by native_decide)

end Hormiga
