/-
  ARCHIVO GENERADO por herencia/gen_herencia.py.
  Los mismos certificados del árbol de casos, re-verificados con `verificaU` (regla levantada: los colores
  cuentan visitas). Resultado: para m = 2j+1 y n ≥ m, la hormiga levantada U(n, m) es una autopista con el
  periodo de la ley y nunca lee un color mayor que (n + m) + n.
-/
import Hormiga.Certificados
import Hormiga.SimbolicoU

namespace Hormiga

/-- Autopista de la ley para la regla levantada, y cota de visitas: ningún color leído pasa de N + n. -/
def BuenoH (n j : Nat) : Prop :=
  (∀ k, lee (RU n (2 * j + 1)) blanco.toE k ≤ (n + (2 * j + 1)) + n) ∧
  ∃ t1 : Nat, t1 ≤ 204 * (n + 2 * j + 1) ∧
    ∃ d : Pt, EsAutopista (RU n (2 * j + 1)) (iter (RU n (2 * j + 1)) t1 blanco.toE) (16 * (n + 2 * j + 1) - 20) d

def BuenoHUno (n j : Nat) : Prop :=
  (∀ k, lee (RU n (2 * j + 1)) blanco.toE k ≤ (n + (2 * j + 1)) + n) ∧
  ∃ t1 : Nat, t1 ≤ 40 * (n + 2 * j + 1) ∧
    ∃ d : Pt, EsAutopista (RU n (2 * j + 1)) (iter (RU n (2 * j + 1)) t1 blanco.toE) (16 * (n + 2 * j + 1) - 12) d

theorem buenoH2 (n j : Nat) (h : M2 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M2 at h; exact absurd hl (by omega)

theorem buenoH4 (n j : Nat) (h : M4 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M4 at h; exact absurd hl (by omega)

theorem buenoH6 (n j : Nat) (h : M6 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M6 at h; exact absurd hl (by omega)

theorem buenoH8 (n j : Nat) (h : M8 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M8 at h; exact absurd hl (by omega)

theorem buenoH10 (n j : Nat) (h : M10 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M10 at h; exact absurd hl (by omega)

theorem buenoH11 (n j : Nat) (h : M11 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M11 at h; exact absurd hl (by omega)

theorem buenoH12 (n j : Nat) (h : M12 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M12 at h; exact absurd hl (by omega)

theorem buenoH14 (n j : Nat) (h : M14 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M14 at h; exact absurd hl (by omega)

theorem buenoH16 (n j : Nat) (h : M16 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M16 at h; exact absurd hl (by omega)

theorem buenoH18 (n j : Nat) (h : M18 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M18 at h; exact absurd hl (by omega)

theorem buenoH20 (n j : Nat) (h : M20 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M20 at h; exact absurd hl (by omega)

theorem buenoH22 (n j : Nat) (h : M22 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M22 at h; exact absurd hl (by omega)

theorem buenoH25 (n j : Nat) (h : M25 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M25 at h; exact absurd hl (by omega)

theorem buenoH27 (n j : Nat) (h : M27 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M27 at h; exact absurd hl (by omega)

theorem buenoH29 (n j : Nat) (h : M29 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M29 at h; exact absurd hl (by omega)

theorem buenoH30 (n j : Nat) (h : M30 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M30 at h; exact absurd hl (by omega)

theorem buenoH32 (n j : Nat) (h : M32 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M32 at h; exact absurd hl (by omega)

theorem buenoH34 (n j : Nat) (h : M34 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M34 at h; exact absurd hl (by omega)

theorem buenoH36 (n j : Nat) (h : M36 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M36 at h; exact absurd hl (by omega)

theorem buenoH37 (n j : Nat) (h : M37 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M37 at h; exact absurd hl (by omega)

theorem buenoH39 (n j : Nat) (h : M39 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M39 at h; exact absurd hl (by omega)

theorem buenoH41 (n j : Nat) (h : M41 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M41 at h; exact absurd hl (by omega)

theorem buenoH43 (n j : Nat) (h : M43 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M43 at h; exact absurd hl (by omega)

theorem buenoH44 (n j : Nat) (h : M44 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M44 at h; exact absurd hl (by omega)

theorem certU47 : verificaU C47 (expand pre47) (expand per47) ⟨-1, 1⟩ (1) = some (⟨209, 104, 0⟩, ⟨78, 40, 0⟩) := by native_decide
theorem buenoH47 (n j : Nat) (h : M47 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M47 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C47 _ _ _ _ _ _ certU47 q.toNat 0
  have hn : C47.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C47, Aff.ev, hqn, ]; omega
  have hm : C47.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C47, Aff.ev, hqn, ]; omega
  have hK : (C47.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C47, Aff.ev, hqn, ]; omega
  have hP : 2 * (Aff.ev ⟨78, 40, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨209, 104, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key.1⟩

theorem certU48 : verificaU C48 (expand pre48) (expand per48) ⟨-2, 2⟩ (2) = some (⟨225, 104, 16⟩, ⟨172, 80, 16⟩) := by native_decide
theorem buenoH48 (n j : Nat) (h : M48 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M48 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have key := verificaU_ok C48 _ _ _ _ _ _ certU48 q1.toNat q2.toNat
  have hn : C48.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C48, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C48.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C48, Aff.ev, hq1n, hq2n, ]; omega
  have hK : (C48.Kf.ev q1.toNat q2.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C48, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨172, 80, 16⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨225, 104, 16⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU52 : verificaU C52 (expand pre52) (expand per52) ⟨-2, 2⟩ (2) = some (⟨189, 0, 0⟩, ⟨140, 0, 0⟩) := by native_decide
theorem buenoH52 (n j : Nat) (h : M52 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M52 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaU_ok C52 _ _ _ _ _ _ certU52 0 0
  have hn : C52.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C52, Aff.ev, ]; omega
  have hm : C52.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C52, Aff.ev, ]; omega
  have hK : (C52.Kf.ev 0 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C52, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨140, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨189, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU53 : verificaU C53 (expand pre53) (expand per53) ⟨-2, 2⟩ (2) = some (⟨385, 192, 0⟩, ⟨284, 144, 0⟩) := by native_decide
theorem buenoH53 (n j : Nat) (h : M53 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M53 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C53 _ _ _ _ _ _ certU53 q.toNat 0
  have hn : C53.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C53, Aff.ev, hqn, ]; omega
  have hm : C53.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C53, Aff.ev, hqn, ]; omega
  have hK : (C53.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C53, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨284, 144, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨385, 192, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU54 : verificaU C54 (expand pre54) (expand per54) ⟨-2, 2⟩ (2) = some (⟨297, 192, 104⟩, ⟨220, 144, 80⟩) := by native_decide
theorem buenoH54 (n j : Nat) (h : M54 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M54 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have key := verificaU_ok C54 _ _ _ _ _ _ certU54 q1.toNat q2.toNat
  have hn : C54.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C54, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C54.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C54, Aff.ev, hq1n, hq2n, ]; omega
  have hK : (C54.Kf.ev q1.toNat q2.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C54, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨220, 144, 80⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨297, 192, 104⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU57 : verificaU C57 (expand pre57) (expand per57) ⟨-2, 2⟩ (2) = some (⟨281, 0, 264⟩, ⟨204, 0, 192⟩) := by native_decide
theorem buenoH57 (n j : Nat) (h : M57 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M57 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C57 _ _ _ _ _ _ certU57 0 q.toNat
  have hn : C57.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C57, Aff.ev, hqn, ]; omega
  have hm : C57.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C57, Aff.ev, hqn, ]; omega
  have hK : (C57.Kf.ev 0 q.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C57, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨204, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨281, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU58 : verificaU C58 (expand pre58) (expand per58) ⟨-2, 2⟩ (2) = some (⟨369, 0, 264⟩, ⟨268, 0, 192⟩) := by native_decide
theorem buenoH58 (n j : Nat) (h : M58 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M58 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C58 _ _ _ _ _ _ certU58 0 q.toNat
  have hn : C58.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C58, Aff.ev, hqn, ]; omega
  have hm : C58.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C58, Aff.ev, hqn, ]; omega
  have hK : (C58.Kf.ev 0 q.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C58, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨268, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨369, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU59 : verificaU C59 (expand pre59) (expand per59) ⟨-2, 2⟩ (2) = some (⟨457, 0, 264⟩, ⟨332, 0, 192⟩) := by native_decide
theorem buenoH59 (n j : Nat) (h : M59 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M59 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C59 _ _ _ _ _ _ certU59 0 q.toNat
  have hn : C59.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C59, Aff.ev, hqn, ]; omega
  have hm : C59.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C59, Aff.ev, hqn, ]; omega
  have hK : (C59.Kf.ev 0 q.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C59, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨332, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨457, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU60 : verificaU C60 (expand pre60) (expand per60) ⟨-2, 2⟩ (2) = some (⟨473, 192, 88⟩, ⟨348, 144, 64⟩) := by native_decide
theorem buenoH60 (n j : Nat) (h : M60 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M60 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have key := verificaU_ok C60 _ _ _ _ _ _ certU60 q1.toNat q2.toNat
  have hn : C60.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C60, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C60.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C60, Aff.ev, hq1n, hq2n, ]; omega
  have hK : (C60.Kf.ev q1.toNat q2.toNat).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C60, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨348, 144, 64⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨473, 192, 88⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU64 : verificaU C64 (expand pre64) (expand per64) ⟨-1, 1⟩ (1) = some (⟨99, 0, 0⟩, ⟨38, 0, 0⟩) := by native_decide
theorem buenoH64 (n j : Nat) (h : M64 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M64 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaU_ok C64 _ _ _ _ _ _ certU64 0 0
  have hn : C64.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C64, Aff.ev, ]; omega
  have hm : C64.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C64, Aff.ev, ]; omega
  have hK : (C64.Kf.ev 0 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C64, Aff.ev, ]; omega
  have hP : 2 * (Aff.ev ⟨38, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨99, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key.1⟩

theorem certU65 : verificaU C65 (expand pre65) (expand per65) ⟨-2, 2⟩ (2) = some (⟨195, 96, 0⟩, ⟨172, 96, 0⟩) := by native_decide
theorem buenoH65 (n j : Nat) (h : M65 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M65 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C65 _ _ _ _ _ _ certU65 q.toNat 0
  have hn : C65.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C65, Aff.ev, hqn, ]; omega
  have hm : C65.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C65, Aff.ev, hqn, ]; omega
  have hK : (C65.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C65, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨172, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨195, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU66 : verificaU C66 (expand pre66) (expand per66) ⟨-2, 2⟩ (2) = some (⟨131, 96, 0⟩, ⟨108, 96, 0⟩) := by native_decide
theorem buenoH66 (n j : Nat) (h : M66 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M66 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C66 _ _ _ _ _ _ certU66 q.toNat 0
  have hn : C66.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C66, Aff.ev, hqn, ]; omega
  have hm : C66.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C66, Aff.ev, hqn, ]; omega
  have hK : (C66.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C66, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨108, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨131, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU67 : verificaU C67 (expand pre67) (expand per67) ⟨-2, 2⟩ (2) = some (⟨163, 96, 0⟩, ⟨140, 96, 0⟩) := by native_decide
theorem buenoH67 (n j : Nat) (h : M67 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M67 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C67 _ _ _ _ _ _ certU67 q.toNat 0
  have hn : C67.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C67, Aff.ev, hqn, ]; omega
  have hm : C67.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C67, Aff.ev, hqn, ]; omega
  have hK : (C67.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C67, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨140, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨163, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU69 : verificaU C69 (expand pre69) (expand per69) ⟨-2, 2⟩ (2) = some (⟨115, 96, 0⟩, ⟨92, 96, 0⟩) := by native_decide
theorem buenoH69 (n j : Nat) (h : M69 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M69 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C69 _ _ _ _ _ _ certU69 q.toNat 0
  have hn : C69.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C69, Aff.ev, hqn, ]; omega
  have hm : C69.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C69, Aff.ev, hqn, ]; omega
  have hK : (C69.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C69, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨92, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨115, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU70 : verificaU C70 (expand pre70) (expand per70) ⟨-2, 2⟩ (2) = some (⟨147, 96, 0⟩, ⟨124, 96, 0⟩) := by native_decide
theorem buenoH70 (n j : Nat) (h : M70 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M70 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C70 _ _ _ _ _ _ certU70 q.toNat 0
  have hn : C70.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C70, Aff.ev, hqn, ]; omega
  have hm : C70.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C70, Aff.ev, hqn, ]; omega
  have hK : (C70.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C70, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨124, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨147, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU71 : verificaU C71 (expand pre71) (expand per71) ⟨-2, 2⟩ (2) = some (⟨179, 96, 0⟩, ⟨156, 96, 0⟩) := by native_decide
theorem buenoH71 (n j : Nat) (h : M71 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  unfold M71 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C71 _ _ _ _ _ _ certU71 q.toNat 0
  have hn : C71.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C71, Aff.ev, hqn, ]; omega
  have hm : C71.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C71, Aff.ev, hqn, ]; omega
  have hK : (C71.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C71, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨156, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨179, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU74 : verificaU C74 (expand pre74) (expand per74) ⟨1, -1⟩ (3) = some (⟨75, 0, 0⟩, ⟨18, 0, 0⟩) := by native_decide
theorem buenoH74 (n j : Nat) (h : M74 n j) (hl : 2 * j + 1 ≤ n) : BuenoHUno n j := by
  unfold M74 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaU_ok C74 _ _ _ _ _ _ certU74 0 0
  have hn : C74.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C74, Aff.ev, ]; omega
  have hm : C74.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C74, Aff.ev, ]; omega
  have hK : (C74.Kf.ev 0 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C74, Aff.ev, ]; omega
  have hP : 2 * (Aff.ev ⟨18, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨75, 0, 0⟩ 0 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key.1⟩

theorem certU75 : verificaU C75 (expand pre75) (expand per75) ⟨2, -2⟩ (6) = some (⟨171, 80, 0⟩, ⟨68, 32, 0⟩) := by native_decide
theorem buenoH75 (n j : Nat) (h : M75 n j) (hl : 2 * j + 1 ≤ n) : BuenoHUno n j := by
  unfold M75 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C75 _ _ _ _ _ _ certU75 q.toNat 0
  have hn : C75.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C75, Aff.ev, hqn, ]; omega
  have hm : C75.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C75, Aff.ev, hqn, ]; omega
  have hK : (C75.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C75, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨68, 32, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨171, 80, 0⟩ q.toNat 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem certU76 : verificaU C76 (expand pre76) (expand per76) ⟨2, -2⟩ (6) = some (⟨131, 80, 0⟩, ⟨52, 32, 0⟩) := by native_decide
theorem buenoH76 (n j : Nat) (h : M76 n j) (hl : 2 * j + 1 ≤ n) : BuenoHUno n j := by
  unfold M76 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have key := verificaU_ok C76 _ _ _ _ _ _ certU76 q.toNat 0
  have hn : C76.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C76, Aff.ev, hqn, ]; omega
  have hm : C76.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C76, Aff.ev, hqn, ]; omega
  have hK : (C76.Kf.ev q.toNat 0).toNat = (n + (2 * j + 1)) + n := by
    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C76, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨52, 32, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨131, 80, 0⟩ q.toNat 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key
  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩

theorem buenoH73 (n j : Nat) (h : M73 n j) (hl : 2 * j + 1 ≤ n) : BuenoHUno n j := by
  rcases cubre73 n j h with h | h
  · exact buenoH74 n j h hl
  · exact buenoH75 n j h hl

theorem buenoH72 (n j : Nat) (h : M72 n j) (hl : 2 * j + 1 ≤ n) : BuenoHUno n j := by
  rcases cubre72 n j h with h | h
  · exact buenoH73 n j h hl
  · exact buenoH76 n j h hl

theorem buenoH68 (n j : Nat) (h : M68 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre68 n j h with h | h | h
  · exact buenoH69 n j h hl
  · exact buenoH70 n j h hl
  · exact buenoH71 n j h hl

theorem buenoH63 (n j : Nat) (h : M63 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre63 n j h with h | h
  · exact buenoH64 n j h hl
  · exact buenoH65 n j h hl

theorem buenoH62 (n j : Nat) (h : M62 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre62 n j h with h | h | h
  · exact buenoH63 n j h hl
  · exact buenoH66 n j h hl
  · exact buenoH67 n j h hl

theorem buenoH61 (n j : Nat) (h : M61 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre61 n j h with h | h
  · exact buenoH62 n j h hl
  · exact buenoH68 n j h hl

theorem buenoH56 (n j : Nat) (h : M56 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre56 n j h with h | h | h
  · exact buenoH57 n j h hl
  · exact buenoH58 n j h hl
  · exact buenoH59 n j h hl

theorem buenoH55 (n j : Nat) (h : M55 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre55 n j h with h | h
  · exact buenoH56 n j h hl
  · exact buenoH60 n j h hl

theorem buenoH51 (n j : Nat) (h : M51 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre51 n j h with h | h
  · exact buenoH52 n j h hl
  · exact buenoH53 n j h hl

theorem buenoH50 (n j : Nat) (h : M50 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre50 n j h with h | h
  · exact buenoH51 n j h hl
  · exact buenoH54 n j h hl

theorem buenoH49 (n j : Nat) (h : M49 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre49 n j h with h | h
  · exact buenoH50 n j h hl
  · exact buenoH55 n j h hl

theorem buenoH46 (n j : Nat) (h : M46 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre46 n j h with h | h
  · exact buenoH47 n j h hl
  · exact buenoH48 n j h hl

theorem buenoH45 (n j : Nat) (h : M45 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre45 n j h with h | h
  · exact buenoH46 n j h hl
  · exact buenoH49 n j h hl

theorem buenoH42 (n j : Nat) (h : M42 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre42 n j h with h | h
  · exact buenoH43 n j h hl
  · exact buenoH44 n j h hl

theorem buenoH40 (n j : Nat) (h : M40 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre40 n j h with h | h
  · exact buenoH41 n j h hl
  · exact buenoH42 n j h hl

theorem buenoH38 (n j : Nat) (h : M38 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre38 n j h with h | h
  · exact buenoH39 n j h hl
  · exact buenoH40 n j h hl

theorem buenoH35 (n j : Nat) (h : M35 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre35 n j h with h | h
  · exact buenoH36 n j h hl
  · exact buenoH37 n j h hl

theorem buenoH33 (n j : Nat) (h : M33 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre33 n j h with h | h
  · exact buenoH34 n j h hl
  · exact buenoH35 n j h hl

theorem buenoH31 (n j : Nat) (h : M31 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre31 n j h with h | h
  · exact buenoH32 n j h hl
  · exact buenoH33 n j h hl

theorem buenoH28 (n j : Nat) (h : M28 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre28 n j h with h | h
  · exact buenoH29 n j h hl
  · exact buenoH30 n j h hl

theorem buenoH26 (n j : Nat) (h : M26 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre26 n j h with h | h
  · exact buenoH27 n j h hl
  · exact buenoH28 n j h hl

theorem buenoH24 (n j : Nat) (h : M24 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre24 n j h with h | h
  · exact buenoH25 n j h hl
  · exact buenoH26 n j h hl

theorem buenoH23 (n j : Nat) (h : M23 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre23 n j h with h | h | h
  · exact buenoH24 n j h hl
  · exact buenoH31 n j h hl
  · exact buenoH38 n j h hl

theorem buenoH21 (n j : Nat) (h : M21 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre21 n j h with h | h
  · exact buenoH22 n j h hl
  · exact buenoH23 n j h hl

theorem buenoH19 (n j : Nat) (h : M19 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre19 n j h with h | h
  · exact buenoH20 n j h hl
  · exact buenoH21 n j h hl

theorem buenoH17 (n j : Nat) (h : M17 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre17 n j h with h | h
  · exact buenoH18 n j h hl
  · exact buenoH19 n j h hl

theorem buenoH15 (n j : Nat) (h : M15 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre15 n j h with h | h
  · exact buenoH16 n j h hl
  · exact buenoH17 n j h hl

theorem buenoH13 (n j : Nat) (h : M13 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre13 n j h with h | h
  · exact buenoH14 n j h hl
  · exact buenoH15 n j h hl

theorem buenoH9 (n j : Nat) (h : M9 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre9 n j h with h | h | h | h
  · exact buenoH10 n j h hl
  · exact buenoH11 n j h hl
  · exact buenoH12 n j h hl
  · exact buenoH13 n j h hl

theorem buenoH7 (n j : Nat) (h : M7 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre7 n j h with h | h
  · exact buenoH8 n j h hl
  · exact buenoH9 n j h hl

theorem buenoH5 (n j : Nat) (h : M5 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre5 n j h with h | h
  · exact buenoH6 n j h hl
  · exact buenoH7 n j h hl

theorem buenoH3 (n j : Nat) (h : M3 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre3 n j h with h | h
  · exact buenoH4 n j h hl
  · exact buenoH5 n j h hl

theorem buenoH1 (n j : Nat) (h : M1 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre1 n j h with h | h
  · exact buenoH2 n j h hl
  · exact buenoH3 n j h hl

theorem buenoH0 (n j : Nat) (h : M0 n j) (hl : 2 * j + 1 ≤ n) : BuenoH n j := by
  rcases cubre0 n j h with h | h
  · exact buenoH1 n j h hl
  · exact buenoH45 n j h hl

theorem visitas_m5 (n j : Nat) (hj : 2 ≤ j) (hn : 2 * j + 1 ≤ n) : BuenoH n j :=
  buenoH0 n j (by unfold M0; omega) hn

theorem visitas_m3 (n : Nat) (hn : 3 ≤ n) : BuenoH n 1 :=
  buenoH61 n 1 (by unfold M61; omega) (by omega)

theorem visitas_m1 (n : Nat) (hn : 2 ≤ n) : BuenoHUno n 0 :=
  buenoH72 n 0 (by unfold M72; omega) (by omega)

end Hormiga
