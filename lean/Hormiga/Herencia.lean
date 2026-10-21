/-
  Herencia por prefijo: lemas generales (no dependen de la regla concreta).

  Desde el tablero en blanco, una casilla visitada k veces sólo ha leído los colores 0, 1, …, k-1.
  Por eso, si una hormiga nunca lee un color ≥ K, cualquier otra regla que coincida con ella en los
  colores < K recorre exactamente la misma trayectoria.

  * `proy_iter`   : una regla y su "copia" con más colores (letra de c = letra de c mod M) tienen
                    la misma trayectoria.
  * `acople_iter` : si la primera regla nunca lee un color ≥ K, la segunda (que coincide con ella en
                    los colores < K y tiene al menos K colores) sigue la misma trayectoria.
  * `autopista_transfiere` : la propiedad de autopista sólo depende de la trayectoria.
  * `lee_periodica` : en las hipótesis del lema de repetición, el color leído también es periódico.
-/
import Hormiga.Ciclo
import Hormiga.Concreto

namespace Hormiga

/-- Color que lee la hormiga en el paso `k`. -/
def lee (R : Regla) (E : Estado) (k : Nat) : Nat := (iter R k E).cfg (iter R k E).pos

/-- Dos hormigas con la misma trayectoria (posición y dirección en cada paso). -/
def MismaTray (R1 R2 : Regla) (E1 E2 : Estado) : Prop :=
  ∀ k, (iter R1 k E1).pos = (iter R2 k E2).pos ∧ (iter R1 k E1).dir = (iter R2 k E2).dir

/-- `E2` es `E1` con los colores reducidos módulo `M`. -/
def Proy (M : Nat) (E1 E2 : Estado) : Prop :=
  E2.pos = E1.pos ∧ E2.dir = E1.dir ∧ ∀ x, E2.cfg x = E1.cfg x % M

theorem Proy.mismo {M : Nat} {E1 E2 : Estado} (h : Proy M E1 E2) : E1.pos = E2.pos ∧ E1.dir = E2.dir :=
  ⟨h.1.symm, h.2.1.symm⟩

/-! ## Proyección: misma regla con más colores -/

theorem proy_paso (R1 R2 : Regla) (hdvd : R2.N ∣ R1.N) (hder : ∀ c, R1.der c = R2.der (c % R2.N))
    {E1 E2 : Estado} (h : Proy R2.N E1 E2) : Proy R2.N (paso R1 E1) (paso R2 E2) := by
  obtain ⟨hp, hd, hc⟩ := h
  have hread : E2.cfg E2.pos = E1.cfg E1.pos % R2.N := by rw [hp]; exact hc _
  have hturn : R2.der (E2.cfg E2.pos) = R1.der (E1.cfg E1.pos) := by rw [hread, hder]
  refine ⟨?_, ?_, ?_⟩
  · simp only [paso]; rw [hturn, hd, hp]
  · simp only [paso]; rw [hturn, hd]
  · intro x
    simp only [paso]
    unfold upd
    rw [hp]
    by_cases hx : x = E1.pos
    · subst hx
      simp only [ite_true]
      rw [hc, Nat.mod_add_mod, Nat.mod_mod_of_dvd _ hdvd]
    · simp only [hx, ite_false]; exact hc x

theorem proy_iter (R1 R2 : Regla) (hdvd : R2.N ∣ R1.N) (hder : ∀ c, R1.der c = R2.der (c % R2.N)) :
    ∀ (k : Nat) (E1 E2 : Estado), Proy R2.N E1 E2 → Proy R2.N (iter R1 k E1) (iter R2 k E2)
  | 0, _, _, h => h
  | k + 1, E1, E2, h => by
      simp only [iter]
      exact proy_iter R1 R2 hdvd hder k _ _ (proy_paso R1 R2 hdvd hder h)

/-! ## Acople: coincidir en los colores que realmente se leen -/

theorem acople_paso (R1 R2 : Regla) (K : Nat) (hK2 : K ≤ R2.N) (hK1 : K < R1.N)
    (hder : ∀ c, c < K → R2.der c = R1.der c)
    {E1 E2 : Estado} (h : Proy R2.N E1 E2) (hlee : E1.cfg E1.pos < K) :
    Proy R2.N (paso R1 E1) (paso R2 E2) := by
  obtain ⟨hp, hd, hc⟩ := h
  have hread : E2.cfg E2.pos = E1.cfg E1.pos := by
    rw [hp, hc, Nat.mod_eq_of_lt (by omega)]
  have hturn : R2.der (E2.cfg E2.pos) = R1.der (E1.cfg E1.pos) := by rw [hread]; exact hder _ hlee
  refine ⟨?_, ?_, ?_⟩
  · simp only [paso]; rw [hturn, hd, hp]
  · simp only [paso]; rw [hturn, hd]
  · intro x
    simp only [paso]
    unfold upd
    rw [hp]
    by_cases hx : x = E1.pos
    · subst hx
      simp only [ite_true]
      rw [hc, Nat.mod_eq_of_lt (show E1.cfg E1.pos < R2.N by omega),
        Nat.mod_eq_of_lt (show E1.cfg E1.pos + 1 < R1.N by omega)]
    · simp only [hx, ite_false]; exact hc x

theorem acople_iter (R1 R2 : Regla) (K : Nat) (hK2 : K ≤ R2.N) (hK1 : K < R1.N)
    (hder : ∀ c, c < K → R2.der c = R1.der c) :
    ∀ (k : Nat) (E1 E2 : Estado), Proy R2.N E1 E2 → (∀ i, i < k → lee R1 E1 i < K) →
      Proy R2.N (iter R1 k E1) (iter R2 k E2)
  | 0, _, _, h, _ => h
  | k + 1, E1, E2, h, hl => by
      simp only [iter]
      apply acople_iter R1 R2 K hK2 hK1 hder k _ _ (acople_paso R1 R2 K hK2 hK1 hder h (by simpa [lee, iter] using hl 0 (by omega)))
      intro i hi
      simpa [lee, iter] using hl (i + 1) (by omega)

/-- Si la primera hormiga nunca lee un color ≥ K, la segunda sigue exactamente su trayectoria. -/
theorem acople_tray (R1 R2 : Regla) (K : Nat) (hK2 : K ≤ R2.N) (hK1 : K < R1.N)
    (hder : ∀ c, c < K → R2.der c = R1.der c) (E1 E2 : Estado) (h0 : Proy R2.N E1 E2)
    (hl : ∀ i, lee R1 E1 i < K) : MismaTray R1 R2 E1 E2 := by
  intro k
  exact (acople_iter R1 R2 K hK2 hK1 hder k E1 E2 h0 (fun i _ => hl i)).mismo

theorem proy_tray (R1 R2 : Regla) (hdvd : R2.N ∣ R1.N) (hder : ∀ c, R1.der c = R2.der (c % R2.N))
    (E1 E2 : Estado) (h0 : Proy R2.N E1 E2) : MismaTray R1 R2 E1 E2 := by
  intro k
  exact (proy_iter R1 R2 hdvd hder k E1 E2 h0).mismo

theorem MismaTray.symm {R1 R2 : Regla} {E1 E2 : Estado} (h : MismaTray R1 R2 E1 E2) : MismaTray R2 R1 E2 E1 :=
  fun k => ⟨(h k).1.symm, (h k).2.symm⟩

theorem MismaTray.trans {R1 R2 R3 : Regla} {E1 E2 E3 : Estado} (h : MismaTray R1 R2 E1 E2)
    (h' : MismaTray R2 R3 E2 E3) : MismaTray R1 R3 E1 E3 :=
  fun k => ⟨(h k).1.trans (h' k).1, (h k).2.trans (h' k).2⟩

/-- Ser autopista depende sólo de la trayectoria. -/
theorem autopista_transfiere {R1 R2 : Regla} {E1 E2 : Estado} (h : MismaTray R1 R2 E1 E2)
    {t1 P : Nat} {d : Pt} (ha : EsAutopista R1 (iter R1 t1 E1) P d) : EsAutopista R2 (iter R2 t1 E2) P d := by
  intro q i hi
  obtain ⟨h1, h2⟩ := ha q i hi
  rw [← iter_add, ← iter_add] at h1 h2 ⊢
  rw [← (h _).1, ← (h _).1, ← (h _).2, ← (h _).2]
  exact ⟨h1, h2⟩

/-! ## El color leído también se repite -/

theorem lee_periodica (R : Regla) (s : Estado) (P : Nat) (d : Pt) (S : Pt → Prop)
    (hS : ∀ x, S x → S (x + d))
    (hrun : ∀ i, i < P → S (iter R i s).pos)
    (hc : Coincide S d s (iter R P s)) :
    ∀ q i, i < P → lee R s (q * P + i) = lee R s i := by
  have hrep := repeticion R s P d S hS hrun hc
  intro q
  induction q with
  | zero => intro i _; simp
  | succ q ih =>
    intro i hi
    obtain ⟨hcq, hrq⟩ := hrep q
    have hk := iter_coincide R i _ _ hcq (fun j hj => by rw [← iter_add]; exact hrq j (by omega))
    rw [← iter_add, ← iter_add] at hk
    obtain ⟨hp, _, hcf⟩ := hk
    have hSi : S (iter R (q * P + i) s).pos := hrq i hi
    have : lee R s ((q + 1) * P + i) = lee R s (q * P + i) := by
      unfold lee
      rw [hp]; exact hcf _ hSi
    rw [this]; exact ih i hi

/-- Si el color leído se repite con periodo P desde T1 y está acotado hasta T1 + P, está acotado siempre. -/
theorem lee_cota_todo (R : Regla) (E : Estado) (T1 P B : Nat) (hP : 0 < P)
    (hper : ∀ q i, i < P → lee R (iter R T1 E) (q * P + i) = lee R (iter R T1 E) i)
    (hb : ∀ k, k < T1 + P → lee R E k ≤ B) : ∀ k, lee R E k ≤ B := by
  intro k
  rcases Nat.lt_or_ge k (T1 + P) with hk | hk
  · exact hb k hk
  · have hdm := Nat.div_add_mod (k - T1) P
    have hmod : (k - T1) % P < P := Nat.mod_lt _ hP
    have e1 : lee R E k = lee R (iter R T1 E) ((k - T1) / P * P + (k - T1) % P) := by
      unfold lee
      rw [← iter_add, show T1 + ((k - T1) / P * P + (k - T1) % P) = k by rw [Nat.mul_comm] at hdm; omega]
    rw [e1, hper _ _ hmod]
    have e2 : lee R (iter R T1 E) ((k - T1) % P) = lee R E (T1 + (k - T1) % P) := by
      unfold lee; rw [← iter_add]
    rw [e2]
    exact hb _ (by omega)

/-- En un ciclo acelerable, el color leído en la vuelta q es el de la primera vuelta más q·Δ. -/
theorem ciclo_lee (R : Regla) (E0 : Estado) (L r : Nat)
    (hpos : (iter R L E0).pos = E0.pos) (hdir : (iter R L E0).dir = E0.dir)
    (hcond : ∀ i, i < L → ∀ q, q ≤ r →
      VisitaOK R ((iter R i E0).cfg (iter R i E0).pos) (q * cuenta (trayE R L E0) (iter R i E0).pos)) :
    ∀ q i, q ≤ r → i < L →
      lee R E0 (q * L + i) = lee R E0 i + q * cuenta (trayE R L E0) (iter R i E0).pos := by
  intro q i hq hi
  have hE := (ciclo R E0 L r hpos hdir hcond q (by omega)).1
  have hdes : Desfase (fun x => q * cuenta (trayE R L E0) x) E0 (masq E0 q (cuenta (trayE R L E0))) :=
    ⟨rfl, rfl, fun x => rfl⟩
  obtain ⟨hp, _, hc⟩ := iter_desfase R i E0 _ hdes (fun j hj => hcond j (by omega) q hq)
  unfold lee
  rw [iter_add, hE, hp, hc]

end Hormiga
