/-
  Verificador simbólico (paramétrico), demostrado correcto.

  Parámetros enteros s, t ≥ 0. Un "cono" fija n y j (m = 2j+1) como funciones afines de (s, t).
  Los colores son formas afines a + b·s + c·t. Un certificado es una lista de segmentos:
    * `paso`        : un paso de la hormiga (las decisiones se comprueban para TODOS los s, t),
    * `marca`       : olvida el historial (el ciclo siguiente empieza aquí),
    * `acel r`      : el historial completo es un ciclo; se repite r veces (r afín).
  `verificaS` ejecuta el certificado y comprueba el lema de repetición. Su corrección está demostrada,
  así que basta evaluarlo para obtener el teorema para todos los (s, t) a la vez.
-/
import Hormiga.Concreto
import Hormiga.Ciclo

namespace Hormiga

/-! ## Formas afines -/

structure Aff where
  a : Int
  b : Int
  c : Int
deriving DecidableEq, Repr

namespace Aff

def ev (f : Aff) (s t : Nat) : Int := f.a + f.b * s + f.c * t
def k (n : Int) : Aff := ⟨n, 0, 0⟩
instance : Add Aff := ⟨fun f g => ⟨f.a + g.a, f.b + g.b, f.c + g.c⟩⟩
instance : Sub Aff := ⟨fun f g => ⟨f.a - g.a, f.b - g.b, f.c - g.c⟩⟩
def mulN (q : Nat) (f : Aff) : Aff := ⟨q * f.a, q * f.b, q * f.c⟩

@[simp] theorem ev_add (f g : Aff) (s t : Nat) : (f + g).ev s t = f.ev s t + g.ev s t := by
  show (f.a + g.a) + (f.b + g.b) * s + (f.c + g.c) * t = _
  simp only [ev, Int.add_mul]; omega

@[simp] theorem ev_sub (f g : Aff) (s t : Nat) : (f - g).ev s t = f.ev s t - g.ev s t := by
  show (f.a - g.a) + (f.b - g.b) * s + (f.c - g.c) * t = _
  simp only [ev, Int.sub_mul]; omega

@[simp] theorem ev_k (n : Int) (s t : Nat) : (k n).ev s t = n := by simp [ev, k]

@[simp] theorem ev_mulN (q : Nat) (f : Aff) (s t : Nat) : (mulN q f).ev s t = q * f.ev s t := by
  simp only [ev, mulN, Int.mul_add, Int.mul_assoc]

/-- Coeficientes no negativos: entonces la forma es ≥ 0 en todo el cono. -/
def nn (f : Aff) : Bool := decide (0 ≤ f.a) && decide (0 ≤ f.b) && decide (0 ≤ f.c)

theorem nn_ok {f : Aff} (h : f.nn = true) (s t : Nat) : 0 ≤ f.ev s t := by
  simp only [nn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  have hs : (0 : Int) ≤ s := by omega
  have ht : (0 : Int) ≤ t := by omega
  have h1 : 0 ≤ f.b * (s : Int) := Int.mul_nonneg hb hs
  have h2 : 0 ≤ f.c * (t : Int) := Int.mul_nonneg hc ht
  simp only [ev]; omega

theorem nn_add {f g : Aff} (hf : f.nn = true) (hg : g.nn = true) : (f + g).nn = true := by
  simp only [nn, Bool.and_eq_true, decide_eq_true_eq] at *
  show (0 ≤ f.a + g.a ∧ 0 ≤ f.b + g.b) ∧ 0 ≤ f.c + g.c
  omega

theorem nn_mulN {f : Aff} (q : Nat) (hf : f.nn = true) : (mulN q f).nn = true := by
  simp only [nn, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨ha, hb⟩, hc⟩ := hf
  have hq : (0 : Int) ≤ q := by omega
  simp only [nn, mulN, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨decide_eq_true (Int.mul_nonneg hq ha), decide_eq_true (Int.mul_nonneg hq hb)⟩, decide_eq_true (Int.mul_nonneg hq hc)⟩

theorem nn_k {n : Int} (h : 0 ≤ n) : (k n).nn = true := by simp [nn, k, h]

end Aff

/-! ## Conos y la regla RⁿLᵐ con parámetros -/

structure Cono where
  nf : Aff
  jf : Aff
deriving Repr

namespace Cono
def n (C : Cono) (s t : Nat) : Nat := (C.nf.ev s t).toNat
def m (C : Cono) (s t : Nat) : Nat := 2 * (C.jf.ev s t).toNat + 1
def Nf (C : Cono) : Aff := C.nf + Aff.mulN 2 C.jf + Aff.k 1
def R (C : Cono) (s t : Nat) : Regla := RL (C.n s t) (C.m s t)
def ok (C : Cono) : Bool := C.nf.nn && C.jf.nn

theorem n_eq (C : Cono) (h : C.ok = true) (s t : Nat) : ((C.n s t : Nat) : Int) = C.nf.ev s t := by
  simp only [ok, Bool.and_eq_true] at h
  have := Aff.nn_ok h.1 s t
  simp only [n]; omega

theorem N_eq (C : Cono) (h : C.ok = true) (s t : Nat) : (((C.R s t).N : Nat) : Int) = C.Nf.ev s t := by
  simp only [ok, Bool.and_eq_true] at h
  have h1 := Aff.nn_ok h.1 s t
  have h2 := Aff.nn_ok h.2 s t
  simp only [R, RL, n, m, Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]
  omega

theorem der_eq (C : Cono) (s t c : Nat) : (C.R s t).der c = decide (c < C.n s t) := rfl
end Cono

/-! ## Configuraciones simbólicas -/

abbrev CfgA := List (Pt × Aff)

def lookA : CfgA → Pt → Aff
  | [], _ => Aff.k 0
  | (p, v) :: r, x => if x = p then v else lookA r x

def setA (l : CfgA) (p : Pt) (v : Aff) : CfgA := (p, v) :: l.filter (fun q => q.1 != p)

def allNN (l : CfgA) : Bool := l.all (fun q => q.2.nn)

def concA (l : CfgA) (s t : Nat) : Pt → Nat := fun x => ((lookA l x).ev s t).toNat

theorem lookA_filter (l : CfgA) (p x : Pt) (hx : x ≠ p) :
    lookA (l.filter (fun q => q.1 != p)) x = lookA l x := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, v⟩ := hd
    by_cases hq : q = p
    · subst hq
      rw [List.filter_cons]
      simp [lookA, hx, ih]
    · rw [List.filter_cons]
      have hb : ((q, v).1 != p) = true := by simp [hq]
      rw [if_pos hb]
      simp only [lookA]
      rw [ih]

theorem lookA_setA (l : CfgA) (p : Pt) (v : Aff) (x : Pt) :
    lookA (setA l p v) x = if x = p then v else lookA l x := by
  unfold setA
  by_cases hx : x = p
  · subst hx; simp [lookA]
  · simp [lookA, hx, lookA_filter l p x hx]

theorem allNN_filter (l : CfgA) (p : Pt) (h : allNN l = true) : allNN (l.filter (fun q => q.1 != p)) = true := by
  simp only [allNN, List.all_eq_true] at *
  intro q hq; exact h q (List.mem_filter.1 hq).1

theorem allNN_setA {l : CfgA} {p : Pt} {v : Aff} (hl : allNN l = true) (hv : v.nn = true) :
    allNN (setA l p v) = true := by
  have := allNN_filter l p hl
  simp only [allNN, setA, List.all_cons, hv, Bool.true_and] at *
  exact this

theorem lookA_nn {l : CfgA} (h : allNN l = true) (x : Pt) : (lookA l x).nn = true := by
  induction l with
  | nil => exact Aff.nn_k (by omega)
  | cons hd tl ih =>
    obtain ⟨q, v⟩ := hd
    simp only [allNN, List.all_cons, Bool.and_eq_true] at h
    simp only [lookA]
    split
    · exact h.1
    · exact ih h.2

theorem concA_setA (l : CfgA) (p : Pt) (v : Aff) (s t : Nat) :
    concA (setA l p v) s t = upd (concA l s t) p ((v.ev s t).toNat) := by
  funext x; simp only [concA, upd, lookA_setA]; split <;> rfl

/-! ## Estado simbólico y un paso -/

structure SS where
  cfg : CfgA
  pos : Pt
  dir : Fin 4
  time : Aff

def SS.toE (X : SS) (s t : Nat) : Estado := ⟨concA X.cfg s t, X.pos, X.dir⟩

/-- Registro de una visita: casilla, dirección antes del paso, color leído y si giró a la derecha. -/
structure Vis where
  cel : Pt
  dir : Fin 4
  v : Aff
  der : Bool
deriving Repr

def clasif (C : Cono) (v : Aff) : Option Bool :=
  if (C.nf - v - Aff.k 1).nn then some true
  else if (v - C.nf).nn then some false else none

def nuevo (C : Cono) (v : Aff) : Option Aff :=
  if v + Aff.k 1 = C.Nf then some (Aff.k 0)
  else if (C.Nf - v - Aff.k 2).nn then some (v + Aff.k 1) else none

def spaso (C : Cono) (X : SS) : Option (SS × Vis) :=
  match clasif C (lookA X.cfg X.pos), nuevo C (lookA X.cfg X.pos) with
  | some dr, some nv =>
    some (⟨setA X.cfg X.pos nv, X.pos + mov (if dr then X.dir + 1 else X.dir + 3),
           (if dr then X.dir + 1 else X.dir + 3), X.time + Aff.k 1⟩, ⟨X.pos, X.dir, lookA X.cfg X.pos, dr⟩)
  | _, _ => none

theorem clasif_ok {C : Cono} {v : Aff} {dr : Bool} (hC : C.ok = true) (hv : v.nn = true)
    (h : clasif C v = some dr) (s t : Nat) : (C.R s t).der ((v.ev s t).toNat) = dr := by
  have hv0 := Aff.nn_ok hv s t
  have hn := C.n_eq hC s t
  rw [Cono.der_eq]
  unfold clasif at h
  split at h
  · rename_i h1
    have := Aff.nn_ok h1 s t
    simp only [Aff.ev_sub, Aff.ev_k] at this
    cases h; simp; omega
  · split at h
    · rename_i _ h2
      have := Aff.nn_ok h2 s t
      simp only [Aff.ev_sub] at this
      cases h; simp; omega
    · cases h

theorem nuevo_ok {C : Cono} {v nv : Aff} (hC : C.ok = true) (hv : v.nn = true)
    (h : nuevo C v = some nv) (s t : Nat) :
    ((v.ev s t).toNat + 1) % (C.R s t).N = (nv.ev s t).toNat ∧ nv.nn = true := by
  have hv0 := Aff.nn_ok hv s t
  have hN := C.N_eq hC s t
  unfold nuevo at h
  split at h
  · rename_i h1
    cases h
    have : v.ev s t + 1 = C.Nf.ev s t := by rw [← h1]; simp
    refine ⟨?_, Aff.nn_k (by omega)⟩
    simp only [Aff.ev_k]
    have : (v.ev s t).toNat + 1 = (C.R s t).N := by omega
    rw [this, Nat.mod_self]; rfl
  · split at h
    · rename_i _ h2
      cases h
      have := Aff.nn_ok h2 s t
      simp only [Aff.ev_sub, Aff.ev_k] at this
      refine ⟨?_, Aff.nn_add hv (Aff.nn_k (by omega))⟩
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [Aff.ev_add, Aff.ev_k]; omega
    · cases h

theorem spaso_ok {C : Cono} {X X' : SS} {w : Vis} (hC : C.ok = true) (hX : allNN X.cfg = true)
    (h : spaso C X = some (X', w)) (s t : Nat) :
    paso (C.R s t) (X.toE s t) = X'.toE s t ∧ allNN X'.cfg = true ∧ X'.time = X.time + Aff.k 1 ∧
    w.cel = X.pos ∧ w.dir = X.dir ∧ w.v = lookA X.cfg X.pos ∧
    (C.R s t).der ((w.v.ev s t).toNat) = w.der := by
  have hv := lookA_nn hX X.pos
  unfold spaso at h
  split at h
  · rename_i dr nv hcl hnu
    cases h
    obtain ⟨hmod, hnn⟩ := nuevo_ok hC hv hnu s t
    have hder := clasif_ok hC hv hcl s t
    have hread : concA X.cfg s t X.pos = ((lookA X.cfg X.pos).ev s t).toNat := rfl
    refine ⟨?_, allNN_setA hX hnn, rfl, rfl, rfl, rfl, hder⟩
    apply Estado.ext'
    · show upd (concA X.cfg s t) X.pos ((concA X.cfg s t X.pos + 1) % (C.R s t).N) = concA (setA X.cfg X.pos nv) s t
      rw [concA_setA, hread, hmod]
    · show X.pos + mov (if (C.R s t).der (concA X.cfg s t X.pos) then X.dir + 1 else X.dir + 3) =
        X.pos + mov (if dr then X.dir + 1 else X.dir + 3)
      rw [hread, hder]
    · show (if (C.R s t).der (concA X.cfg s t X.pos) then X.dir + 1 else X.dir + 3) =
        (if dr then X.dir + 1 else X.dir + 3)
      rw [hread, hder]
  · cases h

/-! ## Certificados: segmentos, historial y aceleración -/

inductive Seg where
  | paso : Seg
  | marca : Seg
  | acel : Aff → Seg
deriving Repr

structure CS where
  X : SS
  hist : List Vis      -- orden cronológico, desde la última marca o aceleración
  V : List Pt          -- casillas visitadas en el tramo

def cuentaV (l : List Vis) (x : Pt) : Nat := (l.filter (fun w => decide (w.cel = x))).length

def condAcel (C : Cono) (cyc : List Vis) (r : Aff) (w : Vis) : Bool :=
  if w.der then (C.nf - Aff.k 1 - w.v - Aff.mulN (cuentaV cyc w.cel) r).nn
  else (C.Nf - Aff.k 2 - w.v - Aff.mulN (cuentaV cyc w.cel) r).nn

def sumaCiclo (cfg : CfgA) (r : Aff) : List Vis → CfgA
  | [] => cfg
  | w :: rest => sumaCiclo (setA cfg w.cel (lookA cfg w.cel + r)) r rest

def acelera (C : Cono) (st : CS) (r : Aff) : Option CS :=
  match st.hist with
  | [] => none
  | w0 :: _ =>
    if decide (w0.cel = st.X.pos) && decide (w0.dir = st.X.dir) && r.nn &&
        st.hist.all (condAcel C st.hist r) then
      some ⟨⟨sumaCiclo st.X.cfg r st.hist, st.X.pos, st.X.dir, st.X.time + Aff.mulN st.hist.length r⟩,
            [], st.V ++ st.hist.map (·.cel)⟩
    else none

def corre (C : Cono) : List Seg → CS → Option CS
  | [], st => some st
  | Seg.paso :: rest, st =>
    match spaso C st.X with
    | some (X', w) => corre C rest ⟨X', st.hist ++ [w], st.V ++ [st.X.pos]⟩
    | none => none
  | Seg.marca :: rest, st => corre C rest ⟨st.X, [], st.V⟩
  | Seg.acel r :: rest, st =>
    match acelera C st r with
    | some st' => corre C rest st'
    | none => none

/-! ### Lemas del historial -/

/-- `HistOK E l`: la lista `l` describe exactamente los pasos que da la hormiga desde `E`. -/
def HistOK (C : Cono) (s t : Nat) : Estado → List Vis → Prop
  | _, [] => True
  | E, w :: rest => E.pos = w.cel ∧ E.dir = w.dir ∧ E.cfg E.pos = (w.v.ev s t).toNat ∧ w.v.nn = true ∧
      (C.R s t).der ((w.v.ev s t).toNat) = w.der ∧ HistOK C s t (paso (C.R s t) E) rest

theorem HistOK_append (C : Cono) (s t : Nat) (w : Vis) :
    ∀ (l : List Vis) (E : Estado), HistOK C s t E l →
      (let F := iter (C.R s t) l.length E
       F.pos = w.cel ∧ F.dir = w.dir ∧ F.cfg F.pos = (w.v.ev s t).toNat ∧ w.v.nn = true ∧
       (C.R s t).der ((w.v.ev s t).toNat) = w.der) →
      HistOK C s t E (l ++ [w])
  | [], E, _, hw => by simpa [HistOK, iter] using hw
  | x :: rest, E, h, hw => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      refine ⟨h1, h2, h3, h4, h5, ?_⟩
      exact HistOK_append C s t w rest _ h6 (by simpa [iter] using hw)

theorem HistOK_get (C : Cono) (s t : Nat) :
    ∀ (l : List Vis) (E : Estado), HistOK C s t E l → ∀ i, i < l.length →
      ∃ w ∈ l, (iter (C.R s t) i E).pos = w.cel ∧
        (iter (C.R s t) i E).cfg (iter (C.R s t) i E).pos = (w.v.ev s t).toNat ∧ w.v.nn = true ∧
        (C.R s t).der ((w.v.ev s t).toNat) = w.der
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | w :: rest, E, h, 0, _ => by
      obtain ⟨h1, _, h3, h4, h5, _⟩ := h
      exact ⟨w, by simp, by simpa [iter] using h1, by simp [iter]; rw [h1] at h3 ⊢; simpa [h1] using h3, h4, h5⟩
  | w :: rest, E, h, i + 1, hi => by
      obtain ⟨w', hw', hh⟩ := HistOK_get C s t rest _ h.2.2.2.2.2 i (by simp at hi; omega)
      exact ⟨w', List.mem_cons_of_mem _ hw', by simpa [iter] using hh⟩

theorem HistOK_tray (C : Cono) (s t : Nat) :
    ∀ (l : List Vis) (E : Estado), HistOK C s t E l → trayE (C.R s t) l.length E = l.map (·.cel)
  | [], _, _ => rfl
  | w :: rest, E, h => by
      simp only [List.length_cons, trayE, List.map_cons]
      rw [h.1, HistOK_tray C s t rest _ h.2.2.2.2.2]

theorem cuenta_map (l : List Vis) (x : Pt) : cuenta (l.map (·.cel)) x = cuentaV l x := by
  induction l with
  | nil => rfl
  | cons w rest ih =>
    rw [List.map_cons, cuenta_cons, ih]
    unfold cuentaV
    by_cases h : w.cel = x <;> simp [List.filter, h] <;> omega

theorem lookA_sumaCiclo (r : Aff) (s t : Nat) :
    ∀ (l : List Vis) (cfg : CfgA) (x : Pt),
      (lookA (sumaCiclo cfg r l) x).ev s t = (lookA cfg x).ev s t + (cuentaV l x : Int) * r.ev s t
  | [], cfg, x => by simp [sumaCiclo, cuentaV]
  | w :: rest, cfg, x => by
      simp only [sumaCiclo]
      rw [lookA_sumaCiclo r s t rest _ x, lookA_setA]
      unfold cuentaV
      by_cases h : x = w.cel
      · subst h; simp [List.filter, Int.add_mul]; omega
      · have h' : ¬ w.cel = x := fun e => h e.symm
        simp [h, h', List.filter]

theorem allNN_sumaCiclo {r : Aff} (hr : r.nn = true) :
    ∀ (l : List Vis) (cfg : CfgA), allNN cfg = true → allNN (sumaCiclo cfg r l) = true
  | [], _, h => h
  | w :: rest, cfg, h => by
      simp only [sumaCiclo]
      exact allNN_sumaCiclo hr rest _ (allNN_setA h (Aff.nn_add (lookA_nn h _) hr))

/-! ### Invariante de la ejecución -/

/-- Invariante: el estado simbólico describe exactamente la hormiga concreta tras `time` pasos desde `E`,
el historial describe los últimos pasos, y `V` contiene las posiciones visitadas desde el paso `Tv`. -/
def Inv (C : Cono) (s t : Nat) (E : Estado) (Tv : Nat) (st : CS) : Prop :=
  allNN st.X.cfg = true ∧ st.X.time.nn = true ∧
  iter (C.R s t) (st.X.time.ev s t).toNat E = st.X.toE s t ∧
  (∃ T0, T0 + st.hist.length = (st.X.time.ev s t).toNat ∧ HistOK C s t (iter (C.R s t) T0 E) st.hist) ∧
  Tv ≤ (st.X.time.ev s t).toNat ∧
  ∀ i, Tv ≤ i → i < (st.X.time.ev s t).toNat → (iter (C.R s t) i E).pos ∈ st.V

theorem Inv_paso {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st : CS} {X' : SS} {w : Vis}
    (hC : C.ok = true) (hI : Inv C s t E Tv st) (h : spaso C st.X = some (X', w)) :
    Inv C s t E Tv ⟨X', st.hist ++ [w], st.V ++ [st.X.pos]⟩ := by
  obtain ⟨hnn, htnn, hiter, ⟨T0, hT0, hH⟩, hTv, hV⟩ := hI
  obtain ⟨hpaso, hnn', htime, hcel, hdir, hv, hder⟩ := spaso_ok hC hnn h s t
  have ht0 := Aff.nn_ok htnn s t
  have htime_ev : (X'.time.ev s t).toNat = (st.X.time.ev s t).toNat + 1 := by
    rw [htime]; simp only [Aff.ev_add, Aff.ev_k]; omega
  have htnn' : X'.time.nn = true := by rw [htime]; exact Aff.nn_add htnn (Aff.nn_k (by omega))
  have hiter' : iter (C.R s t) (X'.time.ev s t).toNat E = X'.toE s t := by
    rw [htime_ev, iter_succ', hiter, hpaso]
  unfold Inv; dsimp only
  refine ⟨hnn', htnn', hiter', ⟨T0, ?_, ?_⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · apply HistOK_append C s t w st.hist _ hH
    have : iter (C.R s t) st.hist.length (iter (C.R s t) T0 E) = st.X.toE s t := by
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

theorem Inv_marca {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st : CS}
    (hI : Inv C s t E Tv st) : Inv C s t E Tv ⟨st.X, [], st.V⟩ := by
  obtain ⟨hnn, htnn, hiter, _, hTv, hV⟩ := hI
  exact ⟨hnn, htnn, hiter, ⟨(st.X.time.ev s t).toNat, by simp, trivial⟩, hTv, hV⟩

theorem Inv_acel_core {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st : CS} {r : Aff}
    (hC : C.ok = true) (hI : Inv C s t E Tv st) (w0 : Vis) (rest : List Vis) (hhist : st.hist = w0 :: rest)
    (hw0cel : w0.cel = st.X.pos) (hw0dir : w0.dir = st.X.dir) (hrnn : r.nn = true)
    (hall : ∀ w ∈ st.hist, condAcel C st.hist r w = true) :
    Inv C s t E Tv ⟨⟨sumaCiclo st.X.cfg r st.hist, st.X.pos, st.X.dir, st.X.time + Aff.mulN st.hist.length r⟩,
      [], st.V ++ st.hist.map (·.cel)⟩ := by
  obtain ⟨hnn, htnn, hiter, ⟨T0, hT0, hH⟩, hTv, hV⟩ := hI
  -- notación
  have hr0 := Aff.nn_ok hrnn s t
  have hrc : ((r.ev s t).toNat : Int) = r.ev s t := by omega
  have ht0 := Aff.nn_ok htnn s t
  have hEnow : iter (C.R s t) st.hist.length (iter (C.R s t) T0 E) = st.X.toE s t := by
    show iter (C.R s t) st.hist.length (iter (C.R s t) T0 E) = _
    rw [← iter_add, hT0, hiter]
  have hLpos : 0 < st.hist.length := by rw [hhist]; simp
  -- el primer paso del ciclo empieza donde estamos ahora
  have hH0 := hH
  rw [hhist] at hH0
  obtain ⟨hE0pos, hE0dir, -, -, -, -⟩ := hH0
  have hpos : (iter (C.R s t) st.hist.length (iter (C.R s t) T0 E)).pos = (iter (C.R s t) T0 E).pos := by rw [hEnow, hE0pos, hw0cel]; rfl
  have hdir : (iter (C.R s t) st.hist.length (iter (C.R s t) T0 E)).dir = (iter (C.R s t) T0 E).dir := by rw [hEnow, hE0dir, hw0dir]; rfl
  have htray : trayE (C.R s t) st.hist.length (iter (C.R s t) T0 E) = st.hist.map (·.cel) := HistOK_tray C s t st.hist (iter (C.R s t) T0 E) hH
  have hcond : ∀ i, i < st.hist.length → ∀ q, q ≤ (r.ev s t).toNat →
      VisitaOK (C.R s t) ((iter (C.R s t) i (iter (C.R s t) T0 E)).cfg (iter (C.R s t) i (iter (C.R s t) T0 E)).pos) (q * cuenta (trayE (C.R s t) st.hist.length (iter (C.R s t) T0 E)) (iter (C.R s t) i (iter (C.R s t) T0 E)).pos) := by
    intro i hi q hq
    obtain ⟨w, hw, hwpos, hwcfg, hwnn, hwder⟩ := HistOK_get C s t st.hist (iter (C.R s t) T0 E) hH i hi
    rw [hwcfg, hwpos, htray, cuenta_map]
    have hcA := hall w hw
    have hv0 := Aff.nn_ok hwnn s t
    have hn := C.n_eq hC s t
    have hN := C.N_eq hC s t
    have hm : 1 ≤ C.m s t := by simp [Cono.m]
    have hNn : (C.R s t).N = C.n s t + C.m s t := rfl
    have hqΔ : (q * (cuentaV st.hist w.cel) : Nat) ≤ (r.ev s t).toNat * (cuentaV st.hist w.cel) := Nat.mul_le_mul_right _ hq
    unfold condAcel at hcA
    unfold VisitaOK
    rw [Cono.der_eq, Cono.der_eq]
    rw [Cono.der_eq] at hwder
    split at hcA
    · rename_i hd
      have := Aff.nn_ok hcA s t
      simp only [Aff.ev_sub, Aff.ev_k, Aff.ev_mulN] at this
      have h1 : (((r.ev s t).toNat * (cuentaV st.hist w.cel) : Nat) : Int) = ((cuentaV st.hist w.cel) : Int) * r.ev s t := by rw [Int.natCast_mul, hrc, Int.mul_comm]
      rw [hd] at hwder
      simp only [decide_eq_true_eq] at hwder
      refine ⟨?_, ?_, ?_⟩
      · simp only [decide_eq_decide]; constructor <;> intro _ <;> omega
      · omega
      · omega
    · rename_i hd
      have := Aff.nn_ok hcA s t
      simp only [Aff.ev_sub, Aff.ev_k, Aff.ev_mulN] at this
      have h1 : (((r.ev s t).toNat * (cuentaV st.hist w.cel) : Nat) : Int) = ((cuentaV st.hist w.cel) : Int) * r.ev s t := by rw [Int.natCast_mul, hrc, Int.mul_comm]
      simp only [Bool.not_eq_true] at hd
      rw [hd] at hwder
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hwder
      refine ⟨?_, ?_, ?_⟩
      · simp only [decide_eq_decide]; constructor <;> intro _ <;> omega
      · omega
      · omega
  have hcic := ciclo (C.R s t) (iter (C.R s t) T0 E) st.hist.length (r.ev s t).toNat hpos hdir hcond
  have hfin := (hcic ((r.ev s t).toNat + 1) (Nat.le_refl _)).1
  have hone := (hcic 1 (by omega)).1
  rw [Nat.one_mul] at hone
  -- nuevo tiempo
  have hLt : ((st.hist.length : Nat) : Int) * r.ev s t ≥ 0 := Int.mul_nonneg (by omega) hr0
  have htime' : ((st.X.time + Aff.mulN st.hist.length r).ev s t).toNat = (st.X.time.ev s t).toNat + st.hist.length * (r.ev s t).toNat := by
    simp only [Aff.ev_add, Aff.ev_mulN]
    have : ((st.hist.length * (r.ev s t).toNat : Nat) : Int) = (st.hist.length : Int) * r.ev s t := by rw [Int.natCast_mul, hrc]
    omega
  have hiter' : iter (C.R s t) ((st.X.time.ev s t).toNat + st.hist.length * (r.ev s t).toNat) E =
      ⟨concA (sumaCiclo st.X.cfg r st.hist) s t, st.X.pos, st.X.dir⟩ := by
    rw [← hT0, Nat.add_assoc, iter_add]
    show iter (C.R s t) (st.hist.length + st.hist.length * (r.ev s t).toNat) (iter (C.R s t) T0 E) = _
    rw [show st.hist.length + st.hist.length * (r.ev s t).toNat = ((r.ev s t).toNat + 1) * st.hist.length by rw [Nat.succ_mul, Nat.mul_comm]; omega, hfin]
    apply Estado.ext'
    · funext x
      simp only [masq, concA]
      rw [lookA_sumaCiclo, htray, cuenta_map, Nat.add_mul, Nat.one_mul]
      have hx0 := Aff.nn_ok (lookA_nn hnn x) s t
      have hEx : ((lookA st.X.cfg x).ev s t).toNat = (iter (C.R s t) T0 E).cfg x + cuentaV st.hist x := by
        have h := congrArg (fun F : Estado => F.cfg x) (hEnow.symm.trans hone)
        simp only [SS.toE, concA, masq, htray, cuenta_map, Nat.one_mul] at h
        exact h
      have hm : (((r.ev s t).toNat * cuentaV st.hist x : Nat) : Int) = (cuentaV st.hist x : Int) * r.ev s t := by
        rw [Int.natCast_mul, hrc, Int.mul_comm]
      have hc0 : (0 : Int) ≤ (cuentaV st.hist x : Int) * r.ev s t := Int.mul_nonneg (by omega) hr0
      omega
    · show (iter (C.R s t) T0 E).pos = st.X.pos
      rw [← hpos, hEnow]; rfl
    · show (iter (C.R s t) T0 E).dir = st.X.dir
      rw [← hdir, hEnow]; rfl
  unfold Inv; dsimp only
  refine ⟨allNN_sumaCiclo hrnn _ _ hnn, Aff.nn_add htnn (Aff.nn_mulN _ hrnn), ?_, ?_, ?_, ?_⟩
  · show iter (C.R s t) ((st.X.time + Aff.mulN st.hist.length r).ev s t).toNat E = _
    rw [htime', hiter']; rfl
  · exact ⟨((st.X.time + Aff.mulN st.hist.length r).ev s t).toNat, by simp, trivial⟩
  · show Tv ≤ ((st.X.time + Aff.mulN st.hist.length r).ev s t).toNat
    rw [htime']; omega
  · intro i h1 h2
    show (iter (C.R s t) i E).pos ∈ st.V ++ st.hist.map (·.cel)
    rw [htime'] at h2
    rcases Nat.lt_or_ge i (st.X.time.ev s t).toNat with h3 | h3
    · exact List.mem_append_left _ (hV i h1 h3)
    · apply List.mem_append_right
      rw [← htray]
      have hj : i - T0 < ((r.ev s t).toNat + 1) * st.hist.length := by rw [Nat.succ_mul]; rw [Nat.mul_comm]; omega
      have := ciclo_pos (C.R s t) (iter (C.R s t) T0 E) st.hist.length (r.ev s t).toNat hpos hdir hcond (i - T0) hj
      rw [show iter (C.R s t) (i - T0) (iter (C.R s t) T0 E) = iter (C.R s t) i E by
        show iter (C.R s t) (i - T0) (iter (C.R s t) T0 E) = _
        rw [← iter_add, show T0 + (i - T0) = i by omega]] at this
      exact this


theorem Inv_acel {C : Cono} {s t : Nat} {E : Estado} {Tv : Nat} {st st' : CS} {r : Aff}
    (hC : C.ok = true) (hI : Inv C s t E Tv st) (h : acelera C st r = some st') :
    Inv C s t E Tv st' := by
  unfold acelera at h
  split at h
  · cases h
  · rename_i w0 rest hhist
    split at h
    · rename_i hcheck
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcheck
      exact Inv_acel_core hC hI w0 rest hhist h1 h2 h3 h4
    · cases h

theorem corre_ok (C : Cono) (hC : C.ok = true) (s t : Nat) (E : Estado) (Tv : Nat) :
    ∀ (segs : List Seg) (st st' : CS), Inv C s t E Tv st → corre C segs st = some st' → Inv C s t E Tv st'
  | [], st, st', hI, h => by simp [corre] at h; subst h; exact hI
  | Seg.paso :: rest, st, st', hI, h => by
      simp only [corre] at h
      split at h
      · rename_i X' w hs
        exact corre_ok C hC s t E Tv rest _ st' (Inv_paso hC hI hs) h
      · cases h
  | Seg.marca :: rest, st, st', hI, h => by
      simp only [corre] at h
      exact corre_ok C hC s t E Tv rest _ st' (Inv_marca hI) h
  | Seg.acel r :: rest, st, st', hI, h => by
      simp only [corre] at h
      split at h
      · rename_i st'' ha
        exact corre_ok C hC s t E Tv rest _ st' (Inv_acel hC hI ha) h
      · cases h

/-! ## Cierre y teorema principal -/

def cierra (X1 X2 : SS) (V : List Pt) (d : Pt) (f0 : Int) : Bool :=
  decide (X2.pos = X1.pos + d) && decide (X2.dir = X1.dir) && decide (0 ≤ phi d d) &&
  V.all (fun x => decide (f0 ≤ phi d x)) &&
  (X1.cfg.map (fun q : Pt × Aff => q.1) ++ X2.cfg.map (fun q : Pt × Aff => q.1 + (⟨-d.x, -d.y⟩ : Pt))).all
    (fun x => !decide (f0 ≤ phi d x) || lookA X2.cfg (x + d) == lookA X1.cfg x)

theorem lookA_not_mem (l : CfgA) (x : Pt) (h : ∀ q ∈ l, q.1 ≠ x) : lookA l x = Aff.k 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, v⟩ := hd
    have h1 : q ≠ x := h (q, v) (by simp)
    have h2 : x ≠ q := fun e => h1 e.symm
    simp only [lookA, h2, ite_false]
    exact ih (fun r hr => h r (by simp [hr]))

def inicioS (ini : CfgA) (d0 : Fin 4) : SS := ⟨ini, ⟨0, 0⟩, d0, Aff.k 0⟩

def verificaS (C : Cono) (ini : CfgA) (d0 : Fin 4) (pre per : List Seg) (d : Pt) (f0 : Int) : Option (Aff × Aff) :=
  if C.ok && allNN ini then
    match corre C pre ⟨inicioS ini d0, [], []⟩ with
    | some st1 =>
      match corre C per ⟨st1.X, st1.hist, []⟩ with
      | some st2 => if cierra st1.X st2.X st2.V d f0 then some (st1.X.time, st2.X.time - st1.X.time) else none
      | none => none
    | none => none
  else none

theorem verificaS_core (C : Cono) (ini : CfgA) (d0 : Fin 4) (pre per : List Seg) (d : Pt) (f0 : Int)
    (hC : C.ok = true) (hini : allNN ini = true) (st1 st2 : CS)
    (h1 : corre C pre ⟨inicioS ini d0, [], []⟩ = some st1)
    (h2 : corre C per ⟨st1.X, st1.hist, []⟩ = some st2)
    (hc : cierra st1.X st2.X st2.V d f0 = true) (s t : Nat) :
    EsAutopista (C.R s t) (iter (C.R s t) (st1.X.time.ev s t).toNat ⟨concA ini s t, ⟨0, 0⟩, d0⟩)
      ((st2.X.time - st1.X.time).ev s t).toNat d := by
  have I0 : Inv C s t (⟨concA ini s t, ⟨0, 0⟩, d0⟩ : Estado) 0 ⟨inicioS ini d0, [], []⟩ := by
    unfold Inv; dsimp only
    refine ⟨hini, Aff.nn_k (by omega), ?_, ⟨0, by simp [inicioS], trivial⟩, by omega, ?_⟩
    · simp [inicioS, Aff.ev_k, iter, SS.toE]
    · intro i h1 h2; simp [inicioS] at h2
  have I1 := corre_ok C hC s t (⟨concA ini s t, ⟨0, 0⟩, d0⟩ : Estado) 0 pre _ st1 I0 h1
  obtain ⟨hnn1, htnn1, hiter1, hH1, _, _⟩ := I1
  have I1' : Inv C s t (⟨concA ini s t, ⟨0, 0⟩, d0⟩ : Estado) (st1.X.time.ev s t).toNat ⟨st1.X, st1.hist, []⟩ := by
    unfold Inv; dsimp only
    exact ⟨hnn1, htnn1, hiter1, hH1, Nat.le_refl _, fun i h1 h2 => absurd h2 (by omega)⟩
  have I2 := corre_ok C hC s t (⟨concA ini s t, ⟨0, 0⟩, d0⟩ : Estado) (st1.X.time.ev s t).toNat per _ st2 I1' h2
  obtain ⟨hnn2, htnn2, hiter2, _, hT12, hV2⟩ := I2
  simp only [cierra, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hpos, hdir⟩, hdd⟩, hrun⟩, hcells⟩ := hc
  have hP : ((st2.X.time - st1.X.time).ev s t).toNat = (st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat := by
    simp only [Aff.ev_sub]
    have := Aff.nn_ok htnn1 s t
    have := Aff.nn_ok htnn2 s t
    omega
  rw [hP]
  apply autopista_de_repeticion (C.R s t) _ _ d (fun x => f0 ≤ phi d x)
  · intro x hx; show f0 ≤ phi d (x + d); rw [phi_add]; omega
  · intro i hi
    rw [← iter_add]
    exact hrun _ (hV2 ((st1.X.time.ev s t).toNat + i) (by omega) (by omega))
  · rw [← iter_add, show (st1.X.time.ev s t).toNat + ((st2.X.time.ev s t).toNat - (st1.X.time.ev s t).toNat) = (st2.X.time.ev s t).toNat by omega]
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


/-- **Corrección del verificador simbólico.** Si `verificaS` acepta el certificado, entonces para TODOS
los parámetros (s, t) la hormiga RⁿLᵐ del cono, partiendo de `ini`, entra en una autopista con deriva `d`
a partir del paso T1(s,t), con periodo P(s,t). -/
theorem verificaS_ok (C : Cono) (ini : CfgA) (d0 : Fin 4) (pre per : List Seg) (d : Pt) (f0 : Int)
    (T1 P : Aff) (h : verificaS C ini d0 pre per d f0 = some (T1, P)) (s t : Nat) :
    EsAutopista (C.R s t) (iter (C.R s t) (T1.ev s t).toNat ⟨concA ini s t, ⟨0, 0⟩, d0⟩)
      (P.ev s t).toNat d := by
  unfold verificaS at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    split at h
    · rename_i st1 h1
      split at h
      · rename_i st2 h2
        split at h
        · rename_i hc
          cases h
          exact verificaS_core C ini d0 pre per d f0 hok.1 hok.2 st1 st2 h1 h2 hc s t
        · cases h
      · cases h
    · cases h
  · cases h

end Hormiga
