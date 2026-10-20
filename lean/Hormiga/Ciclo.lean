/-
  Lema de ciclos: justifica la "aceleración" del motor simbólico.

  Si en L pasos la hormiga vuelve a la misma posición y dirección, sin que ningún color dé la vuelta,
  y en cada visita del ciclo el color leído sigue en la misma clase (derecha/izquierda) aunque se le
  sumen hasta r vueltas más, entonces repetir el ciclo r veces equivale a sumar r·Δ a los colores,
  donde Δ(x) es el número de visitas a x en el ciclo.
-/
import Hormiga.Basico

namespace Hormiga

theorem Estado.ext' {a b : Estado} (hc : a.cfg = b.cfg) (hp : a.pos = b.pos) (hd : a.dir = b.dir) : a = b := by
  cases a; cases b; simp only at hc hp hd; subst hc; subst hp; subst hd; rfl

/-- `Y` es `X` con los colores aumentados en `off`. -/
def Desfase (off : Pt → Nat) (X Y : Estado) : Prop :=
  Y.pos = X.pos ∧ Y.dir = X.dir ∧ ∀ x, Y.cfg x = X.cfg x + off x

theorem paso_desfase (R : Regla) {off : Pt → Nat} {X Y : Estado} (h : Desfase off X Y)
    (hder : R.der (X.cfg X.pos + off X.pos) = R.der (X.cfg X.pos))
    (hx : X.cfg X.pos + 1 < R.N) (hy : X.cfg X.pos + off X.pos + 1 < R.N) :
    Desfase off (paso R X) (paso R Y) := by
  obtain ⟨hp, hd, hc⟩ := h
  have hread : Y.cfg Y.pos = X.cfg X.pos + off X.pos := by rw [hp]; exact hc _
  refine ⟨?_, ?_, ?_⟩
  · simp only [paso]
    rw [hread, hder, hd, hp]
  · simp only [paso]
    rw [hread, hder, hd]
  · intro x
    simp only [paso]
    rw [hread, hp]
    unfold upd
    by_cases hxp : x = X.pos
    · subst hxp
      simp only [ite_true]
      rw [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx]
      omega
    · simp only [hxp, ite_false]
      exact hc x

/-- Condición de una visita: el color leído `v`, sumándole `o`, conserva la clase y no da la vuelta. -/
def VisitaOK (R : Regla) (v o : Nat) : Prop :=
  R.der (v + o) = R.der v ∧ v + 1 < R.N ∧ v + o + 1 < R.N

theorem iter_desfase (R : Regla) {off : Pt → Nat} :
    ∀ (L : Nat) (X Y : Estado), Desfase off X Y →
      (∀ i, i < L → VisitaOK R ((iter R i X).cfg (iter R i X).pos) (off (iter R i X).pos)) →
      Desfase off (iter R L X) (iter R L Y)
  | 0, _, _, h, _ => h
  | L + 1, X, Y, h, hv => by
      simp only [iter]
      obtain ⟨h1, h2, h3⟩ := hv 0 (by omega)
      apply iter_desfase R L _ _ (paso_desfase R h h1 h2 h3)
      intro i hi
      simpa [iter] using hv (i + 1) (by omega)

/-- Posiciones visitadas en los primeros L pasos. -/
def trayE (R : Regla) : Nat → Estado → List Pt
  | 0, _ => []
  | L + 1, E => E.pos :: trayE R L (paso R E)

def cuenta (l : List Pt) (x : Pt) : Nat := (l.filter (fun y => decide (y = x))).length

theorem cuenta_cons (p : Pt) (l : List Pt) (x : Pt) :
    cuenta (p :: l) x = (if p = x then 1 else 0) + cuenta l x := by
  unfold cuenta; by_cases h : p = x <;> simp [List.filter, h] <;> omega

/-- Sin vueltas de color, L pasos suman a cada casilla su número de visitas. -/
theorem iter_cfg_cuenta (R : Regla) : ∀ (L : Nat) (E : Estado),
    (∀ i, i < L → (iter R i E).cfg (iter R i E).pos + 1 < R.N) →
    ∀ x, (iter R L E).cfg x = E.cfg x + cuenta (trayE R L E) x
  | 0, E, _, x => by simp [iter, trayE, cuenta]
  | L + 1, E, h, x => by
      simp only [iter, trayE]
      rw [iter_cfg_cuenta R L (paso R E) (fun i hi => by simpa [iter] using h (i + 1) (by omega)) x]
      rw [cuenta_cons]
      have h0 := h 0 (by omega)
      simp only [iter] at h0
      simp only [paso]
      unfold upd
      by_cases hx : x = E.pos
      · subst hx; simp only [ite_true]; rw [Nat.mod_eq_of_lt h0]; omega
      · have : ¬ E.pos = x := fun e => hx e.symm
        simp only [hx, this, ite_false]; omega

theorem trayE_get (R : Regla) : ∀ (L : Nat) (E : Estado) (i : Nat), i < L →
    (iter R i E).pos ∈ trayE R L E
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | L + 1, E, 0, _ => by simp [trayE, iter]
  | L + 1, E, i + 1, h => by
      simp only [trayE, iter]
      exact List.mem_cons_of_mem _ (trayE_get R L (paso R E) i (by omega))

/-- Estado con los colores aumentados en q·Δ. -/
def masq (E : Estado) (q : Nat) (Δ : Pt → Nat) : Estado := ⟨fun x => E.cfg x + q * Δ x, E.pos, E.dir⟩

/-- **Lema de ciclos.** -/
theorem ciclo (R : Regla) (E0 : Estado) (L r : Nat)
    (hpos : (iter R L E0).pos = E0.pos) (hdir : (iter R L E0).dir = E0.dir)
    (hcond : ∀ i, i < L → ∀ q, q ≤ r →
      VisitaOK R ((iter R i E0).cfg (iter R i E0).pos) (q * cuenta (trayE R L E0) (iter R i E0).pos)) :
    ∀ q, q ≤ r + 1 → iter R (q * L) E0 = masq E0 q (cuenta (trayE R L E0)) ∧
      ∀ i, i < L → q ≤ r → (iter R (q * L + i) E0).pos = (iter R i E0).pos := by
  let Δ := cuenta (trayE R L E0)
  have hnowrap : ∀ i, i < L → (iter R i E0).cfg (iter R i E0).pos + 1 < R.N :=
    fun i hi => (hcond i hi 0 (Nat.zero_le _)).2.1
  have hone : iter R L E0 = masq E0 1 Δ := by
    apply Estado.ext'
    · funext x; rw [iter_cfg_cuenta R L E0 hnowrap x]; simp [masq, Δ]
    · exact hpos
    · exact hdir
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · apply Estado.ext' <;> simp [iter, masq]
    · intro i _ _; simp
  | succ q ih =>
    intro hq
    obtain ⟨ihE, _⟩ := ih (by omega)
    -- desfase q·Δ entre la primera vuelta y la vuelta q+1
    have hdes : Desfase (fun x => q * Δ x) E0 (masq E0 q Δ) := ⟨rfl, rfl, fun x => rfl⟩
    have hrun := iter_desfase R L E0 (masq E0 q Δ) hdes
      (fun i hi => hcond i hi q (by omega))
    have hstep : iter R ((q + 1) * L) E0 = iter R L (masq E0 q Δ) := by
      rw [Nat.succ_mul, iter_add, ihE]
    have hfirst : iter R ((q + 1) * L) E0 = masq E0 (q + 1) Δ := by
      rw [hstep]
      obtain ⟨hp, hd, hc⟩ := hrun
      apply Estado.ext'
      · funext x; rw [hc x, hone]; simp only [masq, Nat.add_mul, Nat.one_mul]; omega
      · rw [hp, hone]; rfl
      · rw [hd, hone]; rfl
    refine ⟨hfirst, ?_⟩
    intro i hi hqr
    rw [iter_add, hfirst]
    have hdes' : Desfase (fun x => (q + 1) * Δ x) E0 (masq E0 (q + 1) Δ) := ⟨rfl, rfl, fun x => rfl⟩
    exact (iter_desfase R i E0 _ hdes' (fun j hj => hcond j (by omega) (q + 1) hqr)).1

/-- Todas las posiciones de las r+1 vueltas están entre las casillas del ciclo. -/
theorem ciclo_pos (R : Regla) (E0 : Estado) (L r : Nat)
    (hpos : (iter R L E0).pos = E0.pos) (hdir : (iter R L E0).dir = E0.dir)
    (hcond : ∀ i, i < L → ∀ q, q ≤ r →
      VisitaOK R ((iter R i E0).cfg (iter R i E0).pos) (q * cuenta (trayE R L E0) (iter R i E0).pos)) :
    ∀ j, j < (r + 1) * L → (iter R j E0).pos ∈ trayE R L E0 := by
  intro j hj
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp at hj
    · exact h
  have hdm := Nat.div_add_mod j L
  have hmod : j % L < L := Nat.mod_lt j hL
  have hq : j / L ≤ r := by
    have : j / L < r + 1 := (Nat.div_lt_iff_lt_mul hL).2 hj
    omega
  have hcyc := (ciclo R E0 L r hpos hdir hcond (j / L) (by omega)).2 (j % L) hmod hq
  rw [show j / L * L + j % L = j by rw [Nat.mul_comm]; exact hdm] at hcyc
  rw [hcyc]
  exact trayE_get R L E0 (j % L) hmod

end Hormiga
