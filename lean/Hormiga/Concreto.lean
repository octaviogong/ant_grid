/-
  Verificador concreto, demostrado correcto.

  `verifica` es una función booleana que simula la hormiga con listas y comprueba las hipótesis
  del lema de repetición. El teorema `verifica_correcto` dice: si `verifica` devuelve `true`,
  la hormiga (en el modelo matemático de Basico.lean) entra en una autopista.
  Así, cada caso concreto se demuestra evaluando `verifica`.
-/
import Hormiga.Basico

namespace Hormiga

/-! ## Configuraciones finitas como listas -/

abbrev CfgL := List (Pt × Nat)

def look : CfgL → Pt → Nat
  | [], _ => 0
  | (p, v) :: r, x => if x = p then v else look r x

def setL (l : CfgL) (p : Pt) (v : Nat) : CfgL := (p, v) :: l.filter (fun q => q.1 != p)

theorem look_filter (l : CfgL) (p x : Pt) (hx : x ≠ p) :
    look (l.filter (fun q => q.1 != p)) x = look l x := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, v⟩ := hd
    by_cases hq : q = p
    · subst hq
      rw [List.filter_cons]
      simp [look, hx, ih]
    · rw [List.filter_cons]
      have hb : ((q, v).1 != p) = true := by simp [hq]
      rw [if_pos hb]
      simp only [look]
      rw [ih]

theorem look_setL (l : CfgL) (p : Pt) (v : Nat) : look (setL l p v) = upd (look l) p v := by
  funext x
  unfold setL upd
  by_cases hx : x = p
  · subst hx; simp [look]
  · simp [look, hx, look_filter l p x hx]

theorem look_not_mem (l : CfgL) (x : Pt) (h : ∀ q ∈ l, q.1 ≠ x) : look l x = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, v⟩ := hd
    have h1 : q ≠ x := h (q, v) (by simp)
    have h2 : x ≠ q := fun e => h1 e.symm
    simp only [look, h2, ite_false]
    exact ih (fun r hr => h r (by simp [hr]))

structure EL where
  cfg : CfgL
  pos : Pt
  dir : Fin 4

def EL.toE (e : EL) : Estado := ⟨look e.cfg, e.pos, e.dir⟩

def pasoL (R : Regla) (e : EL) : EL :=
  let c := look e.cfg e.pos
  let d : Fin 4 := if R.der c then e.dir + 1 else e.dir + 3
  ⟨setL e.cfg e.pos ((c + 1) % R.N), e.pos + mov d, d⟩

theorem pasoL_ok (R : Regla) (e : EL) : (pasoL R e).toE = paso R e.toE := by
  unfold pasoL paso EL.toE
  rw [look_setL]

def iterL (R : Regla) : Nat → EL → EL
  | 0, e => e
  | k + 1, e => iterL R k (pasoL R e)

theorem iterL_ok (R : Regla) : ∀ (k : Nat) (e : EL), (iterL R k e).toE = iter R k e.toE
  | 0, _ => rfl
  | k + 1, e => by simp only [iterL, iter]; rw [iterL_ok R k (pasoL R e), pasoL_ok]

/-- Posiciones de los primeros `k` pasos. -/
def trayL (R : Regla) : Nat → EL → List Pt
  | 0, _ => []
  | k + 1, e => e.pos :: trayL R k (pasoL R e)

theorem trayL_mem (R : Regla) : ∀ (k : Nat) (e : EL) (i : Nat), i < k → (iter R i e.toE).pos ∈ trayL R k e
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, e, 0, _ => by simp [trayL, iter, EL.toE]
  | k + 1, e, i + 1, h => by
      simp only [trayL, iter]
      rw [← pasoL_ok]
      exact List.mem_cons_of_mem _ (trayL_mem R k (pasoL R e) i (by omega))

/-! ## El verificador -/

def phi (d x : Pt) : Int := x.x * d.x + x.y * d.y

/-- Comprueba, para el estado `e` y los datos (P, d, φ0):
  1. tras P pasos la hormiga está en pos + d con la misma dirección;
  2. 0 ≤ φ(d), así que el semiplano S = {φ ≥ φ0} es cerrado bajo +d;
  3. todas las posiciones del periodo están en S;
  4. en S, la configuración final trasladada coincide con la inicial
     (se revisan solo las casillas no nulas de alguna de las dos; las demás valen 0). -/
def verifica (R : Regla) (e : EL) (P : Nat) (d : Pt) (f0 : Int) : Bool :=
  let e2 := iterL R P e
  decide (e2.pos = e.pos + d) && decide (e2.dir = e.dir) && decide (0 ≤ phi d d) &&
  (trayL R P e).all (fun x => decide (f0 ≤ phi d x)) &&
  (e.cfg.map (fun q : Pt × Nat => q.1) ++ e2.cfg.map (fun q : Pt × Nat => q.1 + (⟨-d.x, -d.y⟩ : Pt))).all
    (fun x => !decide (f0 ≤ phi d x) || look e2.cfg (x + d) == look e.cfg x)

theorem phi_add (d x : Pt) : phi d (x + d) = phi d x + phi d d := by
  simp [phi, Int.add_mul]; omega

theorem verifica_correcto (R : Regla) (e : EL) (P : Nat) (d : Pt) (f0 : Int)
    (h : verifica R e P d f0 = true) : EsAutopista R e.toE P d := by
  simp only [verifica, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hpos, hdir⟩, hdd⟩, hrun⟩, hcells⟩ := h
  let S : Pt → Prop := fun x => f0 ≤ phi d x
  apply autopista_de_repeticion R e.toE P d S
  · intro x hx; show f0 ≤ phi d (x + d); rw [phi_add]; have : f0 ≤ phi d x := hx; omega
  · intro i hi; exact hrun _ (trayL_mem R P e i hi)
  · rw [← iterL_ok]
    refine ⟨hpos, hdir, ?_⟩
    intro x hx
    show look (iterL R P e).cfg (x + d) = look e.cfg x
    by_cases hm : (∃ q ∈ e.cfg, q.1 = x) ∨ (∃ q ∈ (iterL R P e).cfg, q.1 = x + d)
    · have hmem : x ∈ e.cfg.map (fun q : Pt × Nat => q.1) ++ (iterL R P e).cfg.map (fun q : Pt × Nat => q.1 + (⟨-d.x, -d.y⟩ : Pt)) := by
        rcases hm with ⟨q, hq, rfl⟩ | ⟨q, hq, hqx⟩
        · exact List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩)
        · apply List.mem_append_right
          refine List.mem_map.2 ⟨q, hq, ?_⟩
          rw [hqx]; apply Pt.ext' <;> simp <;> omega
      have := hcells x hmem
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at this
      rcases this with hno | heq
      · exact absurd hx hno
      · exact heq
    · simp only [not_or, not_exists, not_and] at hm
      rw [look_not_mem _ _ (fun q hq => hm.2 q hq), look_not_mem _ _ (fun q hq => hm.1 q hq)]

/-! ## La familia RⁿLᵐ -/

/-- Regla RⁿLᵐ: estados 0..n-1 giran a la derecha, n..n+m-1 a la izquierda. -/
def RL (n m : Nat) : Regla := ⟨n + m, fun c => decide (c < n)⟩

/-- Tablero en blanco, hormiga en el origen mirando al norte. -/
def blanco : EL := ⟨[], ⟨0, 0⟩, 0⟩

theorem blanco_toE : blanco.toE = ⟨fun _ => 0, ⟨0, 0⟩, 0⟩ := by
  simp [blanco, EL.toE]; funext x; rfl

/-- Autopista desde el blanco: a partir del paso t1, periodo P y deriva d. -/
theorem autopista_desde_blanco (n m t1 P : Nat) (d : Pt) (f0 : Int)
    (h : verifica (RL n m) (iterL (RL n m) t1 blanco) P d f0 = true) :
    EsAutopista (RL n m) (iter (RL n m) t1 blanco.toE) P d := by
  rw [← iterL_ok]; exact verifica_correcto _ _ P d f0 h

end Hormiga
