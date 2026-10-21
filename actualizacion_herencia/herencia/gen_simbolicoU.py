"""Genera lean/Hormiga/SimbolicoU.lean a partir de Simbolico.lean (mismas pruebas, regla levantada U)."""
import re, os
RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = open(os.path.join(RAIZ, 'lean/Hormiga/Simbolico.lean')).read().split('\n')
def block(a, b): return '\n'.join(src[a-1:b-1])   # líneas [a, b)
def ren(s):
    s = re.sub(r'\bHistOK', 'HistOKU', s)
    s = re.sub(r'\bInv_', 'InvU_', s); s = re.sub(r'\bInv\b', 'InvU', s)
    s = re.sub(r'\bcorre_ok\b', 'correU_ok', s); s = re.sub(r'\bcorre\b', 'correU', s)
    s = re.sub(r'\bacelera\b', 'aceleraU', s); s = re.sub(r'\bcondAcel\b', 'condAcelU', s)
    s = re.sub(r'\bspaso_ok\b', 'spasoU_ok', s); s = re.sub(r'\bspaso\b', 'spasoU', s)
    s = s.replace('C.R s t', 'C.U s t')
    return s
hist = ren(block(313, 350))
acel_core = ren(block(424, 538))
acel = ren(block(538, 553))
corre_ok = ren(block(553, 572))

# --- parches en InvU_acel_core
acel_core = acel_core.replace("obtain ⟨hnn, htnn, hiter, ⟨T0, hT0, hH⟩, hTv, hV⟩ := hI",
                              "obtain ⟨hnn, htnn, hiter, ⟨T0, hT0, hH⟩, hTv, hV, hlee⟩ := hI")
i0 = acel_core.index("    have hcA := hall w hw")
i1 = acel_core.index("  have hcic :=")
nuevo_hcond = """    exact (hvis w hw (iter (C.U s t) i (iter (C.U s t) T0 E)).pos q hq hwder).1
"""
acel_core = acel_core[:i0] + nuevo_hcond + acel_core[i1:]
# hvis: lema auxiliar previo al hcond (visitas del ciclo); se inserta antes de "  have hcond"
j0 = acel_core.index("  have hcond :")
hvis = """  -- cada visita del ciclo: VisitaOK y cota del color leído en todas las vueltas
  have hvis : ∀ w ∈ st.hist, ∀ (x : Pt), ∀ q, q ≤ (r.ev s t).toNat → (C.U s t).der ((w.v.ev s t).toNat) = w.der →
      VisitaOK (C.U s t) (w.v.ev s t).toNat (q * cuentaV st.hist w.cel) ∧
      (w.v.ev s t).toNat + q * cuentaV st.hist w.cel ≤ (C.Kf.ev s t).toNat := by
    intro w hw _ q hq _
    have hwnn : w.v.nn = true := hvnn w hw
    have hcA := hall w hw
    have hv0 := Aff.nn_ok hwnn s t
    have hqΔ : (q * (cuentaV st.hist w.cel) : Nat) ≤ (r.ev s t).toNat * (cuentaV st.hist w.cel) := Nat.mul_le_mul_right _ hq
    have h1 : (((r.ev s t).toNat * (cuentaV st.hist w.cel) : Nat) : Int) = ((cuentaV st.hist w.cel) : Int) * r.ev s t := by
      rw [Int.natCast_mul, hrc, Int.mul_comm]
    have hN := C.NN_eq hC s t
    have hn := C.n_eq hC s t
    have hm : 1 ≤ C.m s t := by simp [Cono.m]
    have hK : C.Kf.ev s t = C.Nf.ev s t + C.nf.ev s t := by simp [Cono.Kf]
    unfold condAcelU at hcA
    cases hint : intervaloU C w.v with
    | none => simp [hint] at hcA
    | some p =>
      obtain ⟨dr, ub⟩ := p
      simp only [hint] at hcA
      have hc2 := Aff.nn_ok hcA s t
      simp only [Aff.ev_sub, Aff.ev_mulN] at hc2
      obtain ⟨hle, hub, hcls⟩ := intervaloU_ok hC hwnn hint s t
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hcls _ (by omega) (by omega), hcls _ (by omega) (by omega)]
      · show _ < 3 * (C.n s t + C.m s t); omega
      · show _ < 3 * (C.n s t + C.m s t); omega
      · omega
"""
acel_core = acel_core[:j0] + hvis + acel_core[j0:]
# hvnn: las visitas del historial tienen color no negativo
k0 = acel_core.index("  have hvis :")
acel_core = acel_core[:k0] + """  have hvnn : ∀ w ∈ st.hist, w.v.nn = true := HistOKU_nn C s t st.hist _ hH
""" + acel_core[k0:]
# en el hcond original: tras rw [hwcfg, hwpos, htray, cuenta_map] usamos hvis
acel_core = acel_core.replace("""    rw [hwcfg, hwpos, htray, cuenta_map]
    exact (hvis w hw (iter (C.U s t) i (iter (C.U s t) T0 E)).pos q hq hwder).1""",
"""    rw [hwcfg, hwpos, htray, cuenta_map]
    exact (hvis w hw w.cel q hq hwder).1""")
# refine final: un conjunto más
acel_core = acel_core.replace("refine ⟨allNN_sumaCiclo hrnn _ _ hnn, Aff.nn_add htnn (Aff.nn_mulN _ hrnn), ?_, ?_, ?_, ?_⟩",
                              "refine ⟨allNN_sumaCiclo hrnn _ _ hnn, Aff.nn_add htnn (Aff.nn_mulN _ hrnn), ?_, ?_, ?_, ?_, ?_⟩")
acel_core = acel_core.rstrip() + """
  · -- colores leídos durante las vueltas aceleradas
    intro i hi
    rw [htime'] at hi
    rcases Nat.lt_or_ge i (st.X.time.ev s t).toNat with h3 | h3
    · exact hlee i h3
    · have hL : 0 < st.hist.length := hLpos
      have hj : i - T0 < ((r.ev s t).toNat + 1) * st.hist.length := by rw [Nat.succ_mul]; rw [Nat.mul_comm]; omega
      have hdm := Nat.div_add_mod (i - T0) st.hist.length
      have hmod : (i - T0) % st.hist.length < st.hist.length := Nat.mod_lt _ hL
      have hq : (i - T0) / st.hist.length ≤ (r.ev s t).toNat := by
        have : (i - T0) / st.hist.length < (r.ev s t).toNat + 1 := (Nat.div_lt_iff_lt_mul hL).2 hj
        omega
      have hcl := ciclo_lee (C.U s t) (iter (C.U s t) T0 E) st.hist.length (r.ev s t).toNat hpos hdir hcond
        ((i - T0) / st.hist.length) ((i - T0) % st.hist.length) hq hmod
      rw [show (i - T0) / st.hist.length * st.hist.length + (i - T0) % st.hist.length = i - T0 by
        rw [Nat.mul_comm]; exact hdm] at hcl
      have e : lee (C.U s t) E i = lee (C.U s t) (iter (C.U s t) T0 E) (i - T0) := by
        unfold lee; rw [← iter_add, show T0 + (i - T0) = i by omega]
      rw [e, hcl]
      obtain ⟨w, hw, hwpos, hwcfg, hwnn, hwder⟩ := HistOKU_get C s t st.hist (iter (C.U s t) T0 E) hH _ hmod
      rw [show lee (C.U s t) (iter (C.U s t) T0 E) ((i - T0) % st.hist.length) = (w.v.ev s t).toNat from hwcfg,
        hwpos, htray, cuenta_map]
      exact (hvis w hw w.cel _ hq hwder).2
"""

head = r'''/-
  ARCHIVO GENERADO por herencia/gen_simbolicoU.py a partir de Simbolico.lean.

  Verificador simbólico para la regla "levantada" U(n, m): 3(n+m) colores, la letra del color c es la de
  c mod (n+m) en RⁿLᵐ. U recorre la misma trayectoria que RⁿLᵐ, pero mientras ningún color llegue a 3(n+m)
  sus colores son los conteos de visitas. El verificador exige además que todo color leído sea ≤ N + n
  (N = n + m), de modo que una ejecución aceptada demuestra a la vez la autopista y la cota de visitas.
-/
import Hormiga.Simbolico
import Hormiga.Herencia

namespace Hormiga

/-- Regla levantada: 3(n+m) colores; gira a la derecha en c si c mod (n+m) < n. -/
def RU (n m : Nat) : Regla := ⟨3 * (n + m), fun c => decide (c % (n + m) < n)⟩

namespace Cono
def U (C : Cono) (s t : Nat) : Regla := RU (C.n s t) (C.m s t)
/-- Color máximo que se permite leer: N + n = K − 1. -/
def Kf (C : Cono) : Aff := C.Nf + C.nf

theorem NN_eq (C : Cono) (h : C.ok = true) (s t : Nat) : ((C.n s t + C.m s t : Nat) : Int) = C.Nf.ev s t :=
  C.N_eq h s t

theorem der_U (C : Cono) (s t x : Nat) : (C.U s t).der x = decide (x % (C.n s t + C.m s t) < C.n s t) := rfl
end Cono

/-- Clasifica un color simbólico en uno de los cuatro intervalos [0,n-1] (R), [n,N-1] (L), [N,N+n-1] (R),
{N+n} (L); devuelve el giro y la cota superior del intervalo. Falla si el color puede pasar de N + n. -/
def intervaloU (C : Cono) (v : Aff) : Option (Bool × Aff) :=
  if (C.nf - Aff.k 1 - v).nn then some (true, C.nf - Aff.k 1)
  else if (v - C.nf).nn && (C.Nf - Aff.k 1 - v).nn then some (false, C.Nf - Aff.k 1)
  else if (v - C.Nf).nn && (C.Kf - Aff.k 1 - v).nn then some (true, C.Kf - Aff.k 1)
  else if (v - C.Kf).nn && (C.Kf - v).nn then some (false, C.Kf)
  else none

theorem intervaloU_ok {C : Cono} {v ub : Aff} {dr : Bool} (hC : C.ok = true) (hv : v.nn = true)
    (h : intervaloU C v = some (dr, ub)) (s t : Nat) :
    v.ev s t ≤ ub.ev s t ∧ ub.ev s t ≤ C.Kf.ev s t ∧
    ∀ x : Nat, v.ev s t ≤ x → (x : Int) ≤ ub.ev s t → (C.U s t).der x = dr := by
  have hv0 := Aff.nn_ok hv s t
  have hn := C.n_eq hC s t
  have hN := C.NN_eq hC s t
  have hm : 1 ≤ C.m s t := by simp [Cono.m]
  have hK : C.Kf.ev s t = C.Nf.ev s t + C.nf.ev s t := by simp [Cono.Kf]
  unfold intervaloU at h
  split at h
  · rename_i h1
    have a1 := Aff.nn_ok h1 s t
    simp only [Aff.ev_sub, Aff.ev_k] at a1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Aff.ev_sub, Aff.ev_k]
    refine ⟨by omega, by omega, ?_⟩
    intro x hx1 hx2
    rw [Cono.der_U, Nat.mod_eq_of_lt (by omega)]
    simp only [decide_eq_true_eq]; omega
  · split at h
    · rename_i _ h2
      simp only [Bool.and_eq_true] at h2
      have a1 := Aff.nn_ok h2.1 s t
      have a2 := Aff.nn_ok h2.2 s t
      simp only [Aff.ev_sub, Aff.ev_k] at a1 a2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Aff.ev_sub, Aff.ev_k]
      refine ⟨by omega, by omega, ?_⟩
      intro x hx1 hx2
      rw [Cono.der_U, Nat.mod_eq_of_lt (by omega)]
      simp only [decide_eq_false_iff_not]; omega
    · split at h
      · rename_i _ _ h3
        simp only [Bool.and_eq_true] at h3
        have a1 := Aff.nn_ok h3.1 s t
        have a2 := Aff.nn_ok h3.2 s t
        simp only [Aff.ev_sub, Aff.ev_k] at a1 a2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Aff.ev_sub, Aff.ev_k]
        refine ⟨by omega, by omega, ?_⟩
        intro x hx1 hx2
        rw [Cono.der_U, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        simp only [decide_eq_true_eq]; omega
      · split at h
        · rename_i _ _ _ h4
          simp only [Bool.and_eq_true] at h4
          have a1 := Aff.nn_ok h4.1 s t
          have a2 := Aff.nn_ok h4.2 s t
          simp only [Aff.ev_sub, Aff.ev_k] at a1 a2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by omega, by omega, ?_⟩
          intro x hx1 hx2
          rw [Cono.der_U, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          simp only [decide_eq_false_iff_not]; omega
        · cases h

def spasoU (C : Cono) (X : SS) : Option (SS × Vis) :=
  match intervaloU C (lookA X.cfg X.pos) with
  | some (dr, _) =>
    some (⟨setA X.cfg X.pos (lookA X.cfg X.pos + Aff.k 1), X.pos + mov (if dr then X.dir + 1 else X.dir + 3),
           (if dr then X.dir + 1 else X.dir + 3), X.time + Aff.k 1⟩, ⟨X.pos, X.dir, lookA X.cfg X.pos, dr⟩)
  | none => none

theorem spasoU_ok {C : Cono} {X X' : SS} {w : Vis} (hC : C.ok = true) (hX : allNN X.cfg = true)
    (h : spasoU C X = some (X', w)) (s t : Nat) :
    paso (C.U s t) (X.toE s t) = X'.toE s t ∧ allNN X'.cfg = true ∧ X'.time = X.time + Aff.k 1 ∧
    w.cel = X.pos ∧ w.dir = X.dir ∧ w.v = lookA X.cfg X.pos ∧
    (C.U s t).der ((w.v.ev s t).toNat) = w.der ∧ (w.v.ev s t).toNat ≤ (C.Kf.ev s t).toNat := by
  have hv := lookA_nn hX X.pos
  have hv0 := Aff.nn_ok hv s t
  have hN := C.NN_eq hC s t
  have hn := C.n_eq hC s t
  have hm : 1 ≤ C.m s t := by simp [Cono.m]
  have hK : C.Kf.ev s t = C.Nf.ev s t + C.nf.ev s t := by simp [Cono.Kf]
  cases hint : intervaloU C (lookA X.cfg X.pos) with
  | none => simp only [spasoU, hint] at h; cases h
  | some p =>
    obtain ⟨dr, ub⟩ := p
    simp only [spasoU, hint, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle, hub, hcls⟩ := intervaloU_ok hC hv hint s t
    have hder : (C.U s t).der ((lookA X.cfg X.pos).ev s t).toNat = dr := hcls _ (by omega) (by omega)
    have hmod : (((lookA X.cfg X.pos).ev s t).toNat + 1) % (C.U s t).N =
        ((lookA X.cfg X.pos + Aff.k 1).ev s t).toNat := by
      show _ % (3 * (C.n s t + C.m s t)) = _
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [Aff.ev_add, Aff.ev_k]; omega
    have hread : concA X.cfg s t X.pos = ((lookA X.cfg X.pos).ev s t).toNat := rfl
    refine ⟨?_, allNN_setA hX (Aff.nn_add hv (Aff.nn_k (by omega))), rfl, rfl, rfl, rfl, hder,
      by show ((lookA X.cfg X.pos).ev s t).toNat ≤ (C.Kf.ev s t).toNat; omega⟩
    apply Estado.ext'
    · show upd (concA X.cfg s t) X.pos ((concA X.cfg s t X.pos + 1) % (C.U s t).N) =
        concA (setA X.cfg X.pos (lookA X.cfg X.pos + Aff.k 1)) s t
      rw [concA_setA, hread, hmod]
    · show X.pos + mov (if (C.U s t).der (concA X.cfg s t X.pos) then X.dir + 1 else X.dir + 3) =
        X.pos + mov (if dr then X.dir + 1 else X.dir + 3)
      rw [hread, hder]
    · show (if (C.U s t).der (concA X.cfg s t X.pos) then X.dir + 1 else X.dir + 3) =
        (if dr then X.dir + 1 else X.dir + 3)
      rw [hread, hder]

def condAcelU (C : Cono) (cyc : List Vis) (r : Aff) (w : Vis) : Bool :=
  match intervaloU C w.v with
  | some (_, ub) => (ub - w.v - Aff.mulN (cuentaV cyc w.cel) r).nn
  | none => false

def aceleraU (C : Cono) (st : CS) (r : Aff) : Option CS :=
  match st.hist with
  | [] => none
  | w0 :: _ =>
    if decide (w0.cel = st.X.pos) && decide (w0.dir = st.X.dir) && r.nn &&
        st.hist.all (condAcelU C st.hist r) then
      some ⟨⟨sumaCiclo st.X.cfg r st.hist, st.X.pos, st.X.dir, st.X.time + Aff.mulN st.hist.length r⟩,
            [], st.V ++ st.hist.map (·.cel)⟩
    else none

def correU (C : Cono) : List Seg → CS → Option CS
  | [], st => some st
  | Seg.paso :: rest, st =>
    match spasoU C st.X with
    | some (X', w) => correU C rest ⟨X', st.hist ++ [w], st.V ++ [st.X.pos]⟩
    | none => none
  | Seg.marca :: rest, st => correU C rest ⟨st.X, [], st.V⟩
  | Seg.acel r :: rest, st =>
    match aceleraU C st r with
    | some st' => correU C rest st'
    | none => none

'''

mid = r'''
theorem HistOKU_nn (C : Cono) (s t : Nat) :
    ∀ (l : List Vis) (E : Estado), HistOKU C s t E l → ∀ w ∈ l, w.v.nn = true
  | [], _, _, w, hw => by simp at hw
  | x :: rest, E, h, w, hw => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · exact h.2.2.2.1
      · exact HistOKU_nn C s t rest _ h.2.2.2.2.2 w hw'

/-- Invariante: como en `Inv`, más la cota de todos los colores leídos hasta ahora. -/
def InvU (C : Cono) (s t : Nat) (E : Estado) (Tv : Nat) (st : CS) : Prop :=
  allNN st.X.cfg = true ∧ st.X.time.nn = true ∧
  iter (C.U s t) (st.X.time.ev s t).toNat E = st.X.toE s t ∧
  (∃ T0, T0 + st.hist.length = (st.X.time.ev s t).toNat ∧ HistOKU C s t (iter (C.U s t) T0 E) st.hist) ∧
  Tv ≤ (st.X.time.ev s t).toNat ∧
  (∀ i, Tv ≤ i → i < (st.X.time.ev s t).toNat → (iter (C.U s t) i E).pos ∈ st.V) ∧
  (∀ i, i < (st.X.time.ev s t).toNat → lee (C.U s t) E i ≤ (C.Kf.ev s t).toNat)

theorem InvU_paso {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st : CS} {X' : SS} {w : Vis}
    (hC : C.ok = true) (hI : InvU C s t E Tv st) (h : spasoU C st.X = some (X', w)) :
    InvU C s t E Tv ⟨X', st.hist ++ [w], st.V ++ [st.X.pos]⟩ := by
  obtain ⟨hnn, htnn, hiter, ⟨T0, hT0, hH⟩, hTv, hV, hlee⟩ := hI
  obtain ⟨hpaso, hnn', htime, hcel, hdir, hv, hder, hbound⟩ := spasoU_ok hC hnn h s t
  have ht0 := Aff.nn_ok htnn s t
  have htime_ev : (X'.time.ev s t).toNat = (st.X.time.ev s t).toNat + 1 := by
    rw [htime]; simp only [Aff.ev_add, Aff.ev_k]; omega
  have htnn' : X'.time.nn = true := by rw [htime]; exact Aff.nn_add htnn (Aff.nn_k (by omega))
  have hiter' : iter (C.U s t) (X'.time.ev s t).toNat E = X'.toE s t := by
    rw [htime_ev, iter_succ', hiter, hpaso]
  unfold InvU; dsimp only
  refine ⟨hnn', htnn', hiter', ⟨T0, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · apply HistOKU_append C s t w st.hist _ hH
    have : iter (C.U s t) st.hist.length (iter (C.U s t) T0 E) = st.X.toE s t := by
      rw [← iter_add, hT0, hiter]
    simp only [this, SS.toE]
    refine ⟨hcel.symm, hdir.symm, ?_, hv ▸ lookA_nn hnn _, hder⟩
    rw [hv]; rfl
  · omega
  · intro i h1 h2
    rw [htime_ev] at h2
    rcases Nat.lt_or_ge i (st.X.time.ev s t).toNat with h3 | h3
    · exact List.mem_append_left _ (hV i h1 h3)
    · have : i = (st.X.time.ev s t).toNat := by omega
      subst this
      rw [hiter]
      exact List.mem_append_right _ (by simp [SS.toE])
  · intro i h2
    rw [htime_ev] at h2
    rcases Nat.lt_or_ge i (st.X.time.ev s t).toNat with h3 | h3
    · exact hlee i h3
    · have : i = (st.X.time.ev s t).toNat := by omega
      subst this
      unfold lee
      rw [hiter]
      show ((lookA st.X.cfg st.X.pos).ev s t).toNat ≤ _
      rw [← hv]; exact hbound

theorem InvU_marca {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st : CS}
    (hI : InvU C s t E Tv st) : InvU C s t E Tv ⟨st.X, [], st.V⟩ := by
  obtain ⟨hnn, htnn, hiter, _, hTv, hV, hlee⟩ := hI
  exact ⟨hnn, htnn, hiter, ⟨(st.X.time.ev s t).toNat, by simp, trivial⟩, hTv, hV, hlee⟩

'''

tail = r'''
/-! ## Verificador U y su corrección -/

def verificaU (C : Cono) (pre per : List Seg) (d : Pt) (f0 : Int) : Option (Aff × Aff) :=
  if C.ok then
    match correU C pre ⟨inicioS [] 0, [], []⟩ with
    | some st1 =>
      match correU C per ⟨st1.X, st1.hist, []⟩ with
      | some st2 =>
        if cierra st1.X st2.X st2.V d f0 && (st2.X.time - st1.X.time - Aff.k 1).nn then
          some (st1.X.time, st2.X.time - st1.X.time)
        else none
      | none => none
    | none => none
  else none

/-- Estado inicial (tablero en blanco) en la forma que usa el verificador. -/
def E0U (s t : Nat) : Estado := ⟨concA [] s t, ⟨0, 0⟩, 0⟩

theorem verificaU_core (C : Cono) (pre per : List Seg) (d : Pt) (f0 : Int)
    (hC : C.ok = true) (st1 st2 : CS)
    (h1 : correU C pre ⟨inicioS [] 0, [], []⟩ = some st1)
    (h2 : correU C per ⟨st1.X, st1.hist, []⟩ = some st2)
    (hc : cierra st1.X st2.X st2.V d f0 = true) (hPpos : (st2.X.time - st1.X.time - Aff.k 1).nn = true)
    (s t : Nat) :
    EsAutopista (C.U s t) (iter (C.U s t) (st1.X.time.ev s t).toNat (E0U s t))
      ((st2.X.time - st1.X.time).ev s t).toNat d ∧
    ∀ k, lee (C.U s t) (E0U s t) k ≤ (C.Kf.ev s t).toNat := by
  have I0 : InvU C s t (E0U s t) 0 ⟨inicioS [] 0, [], []⟩ := by
    unfold InvU; dsimp only
    refine ⟨rfl, Aff.nn_k (by omega), ?_, ⟨0, by simp [inicioS], trivial⟩, by omega, ?_, ?_⟩
    · simp [inicioS, Aff.ev_k, iter, SS.toE, E0U]
    · intro i h1 h2; simp [inicioS] at h2
    · intro i h2; simp [inicioS] at h2
  have I1 := correU_ok C hC s t (E0U s t) 0 pre _ st1 I0 h1
  obtain ⟨hnn1, htnn1, hiter1, hH1, _, _, hlee1⟩ := I1
  have I1' : InvU C s t (E0U s t) (st1.X.time.ev s t).toNat ⟨st1.X, st1.hist, []⟩ := by
    unfold InvU; dsimp only
    exact ⟨hnn1, htnn1, hiter1, hH1, Nat.le_refl _, fun i h1 h2 => absurd h2 (by omega), hlee1⟩
  have I2 := correU_ok C hC s t (E0U s t) (st1.X.time.ev s t).toNat per _ st2 I1' h2
  obtain ⟨hnn2, htnn2, hiter2, _, hT12, hV2, hlee2⟩ := I2
  simp only [cierra, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hpos, hdir⟩, hdd⟩, hrun⟩, hcells⟩ := hc
  have hP : ((st2.X.time - st1.X.time).ev s t).toNat = (st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat := by
    simp only [Aff.ev_sub]
    have := Aff.nn_ok htnn1 s t
    have := Aff.nn_ok htnn2 s t
    omega
  have hPp : 0 < ((st2.X.time - st1.X.time).ev s t).toNat := by
    have := Aff.nn_ok hPpos s t
    simp only [Aff.ev_sub, Aff.ev_k] at this ⊢
    omega
  rw [hP] at hPp ⊢
  -- las tres hipótesis del lema de repetición, con S = semiplano
  have hS : ∀ x, (fun x => f0 ≤ phi d x) x → (fun x => f0 ≤ phi d x) (x + d) := by
    intro x hx
    have hx' : f0 ≤ phi d x := hx
    show f0 ≤ phi d (x + d); rw [phi_add]; omega
  have hrunS : ∀ i, i < (st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat →
      (fun x => f0 ≤ phi d x) (iter (C.U s t) i (iter (C.U s t) (st1.X.time.ev s t).toNat (E0U s t))).pos := by
    intro i hi
    rw [← iter_add]
    exact hrun _ (hV2 ((st1.X.time.ev s t).toNat + i) (by omega) (by omega))
  have hcoin : Coincide (fun x => f0 ≤ phi d x) d (iter (C.U s t) (st1.X.time.ev s t).toNat (E0U s t))
      (iter (C.U s t) ((st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat)
        (iter (C.U s t) (st1.X.time.ev s t).toNat (E0U s t))) := by
    rw [← iter_add, show (st1.X.time.ev s t).toNat + ((st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat) = (st2.X.time.ev s t).toNat by omega]
    rw [hiter2, hiter1]
    refine ⟨hpos, hdir, ?_⟩
    intro x hx
    show concA st2.X.cfg s t (x + d) = concA st1.X.cfg s t x
    simp only [concA]
    by_cases hm : (∃ q ∈ st1.X.cfg, q.1 = x) ∨ (∃ q ∈ st2.X.cfg, q.1 = x + d)
    · have hmem : x ∈ st1.X.cfg.map (fun q : Pt × Aff => q.1) ++ st2.X.cfg.map (fun q : Pt × Aff => q.1 + (⟨-d.x, -d.y⟩ : Pt)) := by
        rcases hm with ⟨q, hq, rfl⟩ | ⟨q, hq, hqx⟩
        · exact List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩)
        · apply List.mem_append_right
          refine List.mem_map.2 ⟨q, hq, ?_⟩
          rw [hqx]; apply Pt.ext' <;> simp <;> omega
      have := hcells x hmem
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at this
      rcases this with hno | heq
      · exact absurd hx hno
      · rw [heq]
    · simp only [not_or, not_exists, not_and] at hm
      rw [lookA_not_mem _ _ (fun q hq => hm.2 q hq), lookA_not_mem _ _ (fun q hq => hm.1 q hq)]
  refine ⟨autopista_de_repeticion (C.U s t) _ _ d _ hS hrunS hcoin, ?_⟩
  -- cota de los colores leídos para todo k: antes del cierre por el invariante, después por periodicidad
  have hper := lee_periodica (C.U s t) _ _ d _ hS hrunS hcoin
  exact lee_cota_todo (C.U s t) (E0U s t) _ _ _ hPp hper (fun k hk => hlee2 k (by omega))

/-- **Corrección del verificador U.** Si acepta el certificado, para todos los (s, t): la hormiga U del cono
es una autopista (deriva d, periodo P, desde T1) y nunca lee un color mayor que N + n. -/
theorem verificaU_ok (C : Cono) (pre per : List Seg) (d : Pt) (f0 : Int) (T1 P : Aff)
    (h : verificaU C pre per d f0 = some (T1, P)) (s t : Nat) :
    EsAutopista (C.U s t) (iter (C.U s t) (T1.ev s t).toNat (E0U s t)) (P.ev s t).toNat d ∧
    ∀ k, lee (C.U s t) (E0U s t) k ≤ (C.Kf.ev s t).toNat := by
  unfold verificaU at h
  split at h
  · rename_i hok
    split at h
    · rename_i st1 h1
      split at h
      · rename_i st2 h2
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          cases h
          exact verificaU_core C pre per d f0 hok st1 st2 h1 h2 hc.1 hc.2 s t
        · cases h
      · cases h
    · cases h
  · cases h

end Hormiga
'''
out = head + hist + '\n' + mid + acel_core + '\n' + acel + '\n' + corre_ok + '\n' + tail
open(os.path.join(RAIZ, 'lean/Hormiga/SimbolicoU.lean'), 'w').write(out)
print('lineas', out.count('\n'))
