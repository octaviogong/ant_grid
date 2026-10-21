/-
  **Teorema de herencia por prefijo.**

  Sea m = 2j + 1 impar y n ≥ m (o m = 1 y n ≥ 2), N = n + m y K = N + n + 1 = 2n + m + 1.
  Toda regla w con al menos K colores cuyas primeras K letras son RⁿLᵐRⁿL — es decir,
  w gira a la derecha en el color c < K exactamente cuando c mod N < n — recorre desde el tablero
  en blanco exactamente la misma trayectoria que RⁿLᵐ. En particular, entra en la autopista de la ley
  (periodo 16(n + m) − 20, o 16n + 4 si m = 1) en el mismo paso.

  Prueba: la regla levantada U(n, m) tiene la trayectoria de RⁿLᵐ (`proy_tray`); los certificados
  re-verificados con `verificaU` muestran que U nunca lee un color ≥ K (`visitas_m5`, `visitas_m3`,
  `visitas_m1`); y entonces w sigue a U (`acople_tray`).
-/
import Hormiga.HerenciaCert

namespace Hormiga

theorem proy_blanco (M : Nat) : Proy M blanco.toE blanco.toE :=
  ⟨rfl, rfl, fun x => by simp [blanco, EL.toE, look]⟩

/-- U(n, m) y RⁿLᵐ tienen la misma trayectoria desde el blanco. -/
theorem U_RL (n m : Nat) : MismaTray (RU n m) (RL n m) blanco.toE blanco.toE :=
  proy_tray (RU n m) (RL n m) ⟨3, by simp [RU, RL, Nat.mul_comm]⟩ (fun _ => rfl) _ _ (proy_blanco _)

/-- Paso común: de la cota de visitas de U a la herencia para w. -/
theorem herencia_de_cota (n m : Nat) (hm : 1 ≤ m) (w : Regla) (hN : 2 * n + m + 1 ≤ w.N)
    (hw : ∀ c, c < 2 * n + m + 1 → w.der c = decide (c % (n + m) < n))
    (hcota : ∀ k, lee (RU n m) blanco.toE k ≤ (n + m) + n) :
    MismaTray (RU n m) w blanco.toE blanco.toE :=
  acople_tray (RU n m) w (2 * n + m + 1) hN (by simp only [RU]; omega) (fun c hc => hw c hc) _ _
    (proy_blanco _) (fun k => by have := hcota k; omega)

/-- **Teorema de herencia** (m = 2j + 1 ≥ 3, n ≥ m). -/
theorem herencia (n j : Nat) (hj : 1 ≤ j) (hn : 2 * j + 1 ≤ n) (w : Regla)
    (hN : 2 * n + (2 * j + 1) + 1 ≤ w.N)
    (hw : ∀ c, c < 2 * n + (2 * j + 1) + 1 → w.der c = decide (c % (n + (2 * j + 1)) < n)) :
    MismaTray (RL n (2 * j + 1)) w blanco.toE blanco.toE ∧
    ∃ t1 : Nat, t1 ≤ 204 * (n + 2 * j + 1) ∧
      ∃ d : Pt, EsAutopista w (iter w t1 blanco.toE) (16 * (n + 2 * j + 1) - 20) d := by
  have hB : BuenoH n j := by
    rcases Nat.lt_or_ge j 2 with h1 | h2
    · have : j = 1 := by omega
      subst this; exact visitas_m3 n hn
    · exact visitas_m5 n j h2 hn
  obtain ⟨hcota, t1, ht1, d, haut⟩ := hB
  have hUw := herencia_de_cota n (2 * j + 1) (by omega) w hN hw hcota
  exact ⟨(U_RL n (2 * j + 1)).symm.trans hUw, t1, ht1, d, autopista_transfiere hUw haut⟩

/-- **Teorema de herencia, familia RⁿL** (n ≥ 2): toda regla que empieza con RⁿLRⁿL. -/
theorem herencia_RnL (n : Nat) (hn : 2 ≤ n) (w : Regla) (hN : 2 * n + 2 ≤ w.N)
    (hw : ∀ c, c < 2 * n + 2 → w.der c = decide (c % (n + 1) < n)) :
    MismaTray (RL n 1) w blanco.toE blanco.toE ∧
    ∃ t1 : Nat, t1 ≤ 40 * (n + 1) ∧ ∃ d : Pt, EsAutopista w (iter w t1 blanco.toE) (16 * n + 4) d := by
  obtain ⟨hcota, t1, ht1, d, haut⟩ := visitas_m1 n hn
  have e1 : 2 * 0 + 1 = 1 := rfl
  rw [e1] at hcota haut
  have hUw := herencia_de_cota n 1 (by omega) w (by omega) (fun c hc => hw c (by omega)) hcota
  refine ⟨(U_RL n 1).symm.trans hUw, t1, by omega, d, ?_⟩
  have e2 : 16 * (n + 2 * 0 + 1) - 12 = 16 * n + 4 := by omega
  rw [e2] at haut
  exact autopista_transfiere hUw haut

/-! ## Versión con palabras: reglas escritas como listas de letras -/

/-- Regla dada por su palabra: `true` = R, `false` = L. -/
def reglaL (l : List Bool) : Regla := ⟨l.length, fun c => l.getD c false⟩

/-- La palabra RⁿLᵐRⁿL. -/
def prefijo (n m : Nat) : List Bool :=
  List.replicate n true ++ List.replicate m false ++ List.replicate n true ++ [false]

theorem prefijo_length (n m : Nat) : (prefijo n m).length = 2 * n + m + 1 := by
  simp [prefijo]; omega

theorem getD_prefijo (n m : Nat) (hm : 1 ≤ m) (c : Nat) (hc : c < 2 * n + m + 1) (resto : List Bool) :
    (prefijo n m ++ resto).getD c false = decide (c % (n + m) < n) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [prefijo_length]; exact hc)]
  simp only [prefijo, List.append_assoc]
  rcases Nat.lt_or_ge c n with h1 | h1
  · rw [List.getElem?_append_left (by simp; exact h1), Nat.mod_eq_of_lt (show c < n + m by omega)]
    simp [h1]
  rw [List.getElem?_append_right (by simp; exact h1)]
  simp only [List.length_replicate]
  rcases Nat.lt_or_ge (c - n) m with h2 | h2
  · rw [List.getElem?_append_left (by simp; exact h2), Nat.mod_eq_of_lt (show c < n + m by omega)]
    simp [h2]; omega
  rw [List.getElem?_append_right (by simp; exact h2)]
  simp only [List.length_replicate]
  rcases Nat.lt_or_ge (c - n - m) n with h3 | h3
  · rw [List.getElem?_append_left (by simp; exact h3)]
    have : c % (n + m) = c - (n + m) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [this]
    simp [h3]; omega
  rw [List.getElem?_append_right (by simp; exact h3)]
  simp only [List.length_replicate]
  have : c % (n + m) = n := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  rw [this, show c - n - m - n = 0 by omega]
  simp

/-- **Corolario.** Para m = 2j + 1 ≥ 3 y n ≥ m: toda palabra que empieza con RⁿLᵐRⁿL, con cualquier
continuación, recorre desde el blanco la trayectoria de RⁿLᵐ y entra en su autopista. -/
theorem herencia_palabra (n j : Nat) (hj : 1 ≤ j) (hn : 2 * j + 1 ≤ n) (resto : List Bool) :
    MismaTray (RL n (2 * j + 1)) (reglaL (prefijo n (2 * j + 1) ++ resto)) blanco.toE blanco.toE ∧
    ∃ t1 : Nat, t1 ≤ 204 * (n + 2 * j + 1) ∧
      ∃ d : Pt, EsAutopista (reglaL (prefijo n (2 * j + 1) ++ resto))
        (iter (reglaL (prefijo n (2 * j + 1) ++ resto)) t1 blanco.toE) (16 * (n + 2 * j + 1) - 20) d :=
  herencia n j hj hn _ (by simp only [reglaL, List.length_append, prefijo_length]; omega)
    (fun c hc => getD_prefijo n (2 * j + 1) (by omega) c hc resto)

/-- **Corolario, familia RⁿL.** Toda palabra que empieza con RⁿLRⁿL (n ≥ 2). -/
theorem herencia_palabra_RnL (n : Nat) (hn : 2 ≤ n) (resto : List Bool) :
    MismaTray (RL n 1) (reglaL (prefijo n 1 ++ resto)) blanco.toE blanco.toE ∧
    ∃ t1 : Nat, t1 ≤ 40 * (n + 1) ∧
      ∃ d : Pt, EsAutopista (reglaL (prefijo n 1 ++ resto)) (iter (reglaL (prefijo n 1 ++ resto)) t1 blanco.toE)
        (16 * n + 4) d :=
  herencia_RnL n hn _ (by simp only [reglaL, List.length_append, prefijo_length]; omega)
    (fun c hc => getD_prefijo n 1 (by omega) c (by omega) resto)

end Hormiga
