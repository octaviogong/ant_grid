/-
  Verificador concreto rápido, demostrado correcto.

  Igual que `verifica` (Concreto.lean), pero el tablero es una tabla hash (`Std.HashMap`) en lugar de
  una lista, así que cada paso cuesta O(1) y no O(tamaño del tablero). Sirve para autopistas que
  empiezan después de millones de pasos.
-/
import Std.Data.HashMap
import Hormiga.Concreto

namespace Hormiga
open Std

instance : Hashable Pt := ⟨fun p => mixHash (hash p.x) (hash p.y)⟩

abbrev CfgH := HashMap Pt Nat

def lookH (m : CfgH) (x : Pt) : Nat := m.getD x 0

theorem lookH_insert (m : CfgH) (p : Pt) (v : Nat) : lookH (m.insert p v) = upd (lookH m) p v := by
  funext x
  unfold lookH upd
  rw [HashMap.getD_insert]
  by_cases hx : x = p
  · subst hx; simp
  · have : (p == x) = false := by simp; exact fun h => hx h.symm
    simp [this, hx]

theorem lookH_not_mem (m : CfgH) (x : Pt) (h : ¬ x ∈ m) : lookH m x = 0 := by
  unfold lookH; exact HashMap.getD_eq_fallback h

structure EH where
  cfg : CfgH
  pos : Pt
  dir : Fin 4

def EH.toE (e : EH) : Estado := ⟨lookH e.cfg, e.pos, e.dir⟩

def pasoH (R : Regla) (e : EH) : EH :=
  let c := lookH e.cfg e.pos
  let d : Fin 4 := if R.der c then e.dir + 1 else e.dir + 3
  ⟨e.cfg.insert e.pos ((c + 1) % R.N), e.pos + mov d, d⟩

theorem pasoH_ok (R : Regla) (e : EH) : (pasoH R e).toE = paso R e.toE := by
  unfold pasoH paso EH.toE
  rw [lookH_insert]

def iterH (R : Regla) : Nat → EH → EH
  | 0, e => e
  | k + 1, e => iterH R k (pasoH R e)

theorem iterH_ok (R : Regla) : ∀ (k : Nat) (e : EH), (iterH R k e).toE = iter R k e.toE
  | 0, _ => rfl
  | k + 1, e => by simp only [iterH, iter]; rw [iterH_ok R k (pasoH R e), pasoH_ok]

def trayH (R : Regla) : Nat → EH → List Pt
  | 0, _ => []
  | k + 1, e => e.pos :: trayH R k (pasoH R e)

theorem trayH_mem (R : Regla) : ∀ (k : Nat) (e : EH) (i : Nat), i < k → (iter R i e.toE).pos ∈ trayH R k e
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, e, 0, _ => by simp [trayH, iter, EH.toE]
  | k + 1, e, i + 1, h => by
      simp only [trayH, iter]
      rw [← pasoH_ok]
      exact List.mem_cons_of_mem _ (trayH_mem R k (pasoH R e) i (by omega))

/-- Las mismas cuatro comprobaciones que `verifica`, con el tablero en tabla hash. -/
def verificaH (R : Regla) (e : EH) (P : Nat) (d : Pt) (f0 : Int) : Bool :=
  let e2 := iterH R P e
  decide (e2.pos = e.pos + d) && decide (e2.dir = e.dir) && decide (0 ≤ phi d d) &&
  (trayH R P e).all (fun x => decide (f0 ≤ phi d x)) &&
  (e.cfg.keys ++ e2.cfg.keys.map (fun q : Pt => q + (⟨-d.x, -d.y⟩ : Pt))).all
    (fun x => !decide (f0 ≤ phi d x) || lookH e2.cfg (x + d) == lookH e.cfg x)

theorem verificaH_correcto (R : Regla) (e : EH) (P : Nat) (d : Pt) (f0 : Int)
    (h : verificaH R e P d f0 = true) : EsAutopista R e.toE P d := by
  simp only [verificaH, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hpos, hdir⟩, hdd⟩, hrun⟩, hcells⟩ := h
  let S : Pt → Prop := fun x => f0 ≤ phi d x
  apply autopista_de_repeticion R e.toE P d S
  · intro x hx; show f0 ≤ phi d (x + d); rw [phi_add]; have : f0 ≤ phi d x := hx; omega
  · intro i hi; exact hrun _ (trayH_mem R P e i hi)
  · rw [← iterH_ok]
    refine ⟨hpos, hdir, ?_⟩
    intro x hx
    show lookH (iterH R P e).cfg (x + d) = lookH e.cfg x
    by_cases hm : x ∈ e.cfg ∨ (x + d) ∈ (iterH R P e).cfg
    · have hmem : x ∈ e.cfg.keys ++ (iterH R P e).cfg.keys.map (fun q : Pt => q + (⟨-d.x, -d.y⟩ : Pt)) := by
        rcases hm with h1 | h2
        · exact List.mem_append_left _ (HashMap.mem_keys.2 h1)
        · apply List.mem_append_right
          refine List.mem_map.2 ⟨x + d, HashMap.mem_keys.2 h2, ?_⟩
          apply Pt.ext' <;> simp <;> omega
      have := hcells x hmem
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at this
      rcases this with hno | heq
      · exact absurd hx hno
      · exact heq
    · simp only [not_or] at hm
      rw [lookH_not_mem _ _ hm.2, lookH_not_mem _ _ hm.1]

/-- Tablero en blanco con tabla hash vacía. -/
def blancoH : EH := ⟨∅, ⟨0, 0⟩, 0⟩

theorem blancoH_toE : blancoH.toE = blanco.toE := by
  rw [blanco_toE]; simp only [blancoH, EH.toE]; congr 1; funext x; simp [lookH]

/-- Autopista desde el blanco, comprobada con el verificador rápido. -/
theorem autopista_desde_blancoH (R : Regla) (t1 P : Nat) (d : Pt) (f0 : Int)
    (h : verificaH R (iterH R t1 blancoH) P d f0 = true) :
    EsAutopista R (iter R t1 blanco.toE) P d := by
  rw [← blancoH_toE, ← iterH_ok]; exact verificaH_correcto _ _ P d f0 h

end Hormiga
