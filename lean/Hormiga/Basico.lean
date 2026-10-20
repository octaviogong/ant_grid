/-
  Hormiga generalizada: modelo y lema de repetición (autopista).

  Todo en Lean 4 puro (sin Mathlib). Nada aquí depende de la regla concreta:
  vale para cualquier hormiga con N colores y cualquier función de giro.
-/
namespace Hormiga

/-- Punto de la cuadrícula ℤ². -/
structure Pt where
  x : Int
  y : Int
deriving DecidableEq, Repr

instance : Add Pt := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩

@[simp] theorem Pt.add_x (a b : Pt) : (a + b).x = a.x + b.x := rfl
@[simp] theorem Pt.add_y (a b : Pt) : (a + b).y = a.y + b.y := rfl

theorem Pt.ext' {a b : Pt} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp only at hx hy; subst hx; subst hy; rfl

theorem Pt.add_right_cancel' {a b d : Pt} (h : a + d = b + d) : a = b := by
  have hx := congrArg Pt.x h; have hy := congrArg Pt.y h
  simp only [Pt.add_x, Pt.add_y] at hx hy
  exact Pt.ext' (by omega) (by omega)

/-- q·d con q natural. -/
def Pt.smul (q : Nat) (d : Pt) : Pt := ⟨(q : Int) * d.x, (q : Int) * d.y⟩

/-- Direcciones: 0 = norte, 1 = este, 2 = sur, 3 = oeste. -/
def mov (i : Fin 4) : Pt :=
  if i.val = 0 then ⟨0, 1⟩ else if i.val = 1 then ⟨1, 0⟩ else if i.val = 2 then ⟨0, -1⟩ else ⟨-1, 0⟩

/-- Una regla: N colores y, para cada color, si la hormiga gira a la derecha (true) o a la izquierda. -/
structure Regla where
  N : Nat
  der : Nat → Bool

/-- Estado: colores de todas las casillas, posición y dirección de la hormiga. -/
structure Estado where
  cfg : Pt → Nat
  pos : Pt
  dir : Fin 4

def upd (f : Pt → Nat) (p : Pt) (v : Nat) : Pt → Nat := fun x => if x = p then v else f x

/-- Un paso: lee el color, gira, incrementa el color (mod N) y avanza. -/
def paso (R : Regla) (s : Estado) : Estado :=
  let c := s.cfg s.pos
  let d : Fin 4 := if R.der c then s.dir + 1 else s.dir + 3
  { cfg := upd s.cfg s.pos ((c + 1) % R.N), pos := s.pos + mov d, dir := d }

/-- k pasos. -/
def iter (R : Regla) : Nat → Estado → Estado
  | 0, s => s
  | k + 1, s => iter R k (paso R s)

theorem iter_add (R : Regla) : ∀ (a b : Nat) (s : Estado), iter R (a + b) s = iter R b (iter R a s)
  | 0, b, s => by simp [iter]
  | a + 1, b, s => by
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [iter]
      exact iter_add R a b (paso R s)

theorem iter_succ' (R : Regla) (k : Nat) (s : Estado) : iter R (k + 1) s = paso R (iter R k s) := by
  rw [iter_add]; rfl

/-! ## Lema de repetición -/

/-- `b` es la copia de `a` trasladada por `d`, al menos en el conjunto `S`. -/
def Coincide (S : Pt → Prop) (d : Pt) (a b : Estado) : Prop :=
  b.pos = a.pos + d ∧ b.dir = a.dir ∧ ∀ x, S x → b.cfg (x + d) = a.cfg x

/-- Si las dos hormigas coinciden en `S` y la primera está dentro de `S`, siguen coincidiendo tras un paso. -/
theorem paso_coincide (R : Regla) {S : Pt → Prop} {d : Pt} {a b : Estado}
    (h : Coincide S d a b) (ha : S a.pos) : Coincide S d (paso R a) (paso R b) := by
  obtain ⟨hp, hd, hc⟩ := h
  have hread : b.cfg b.pos = a.cfg a.pos := by rw [hp]; exact hc _ ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [paso]
    rw [hread, hd, hp]
    apply Pt.ext' <;> simp <;> omega
  · simp only [paso]
    rw [hread, hd]
  · intro x hx
    simp only [paso]
    rw [hread]
    unfold upd
    by_cases hxa : x = a.pos
    · subst hxa; simp [hp]
    · have hne : x + d ≠ b.pos := by
        intro h; apply hxa; rw [hp] at h; exact Pt.add_right_cancel' h
      simp only [hxa, hne, ite_false]
      exact hc x hx

/-- Versión iterada: mientras la primera hormiga no salga de `S`, siguen coincidiendo. -/
theorem iter_coincide (R : Regla) {S : Pt → Prop} {d : Pt} :
    ∀ (k : Nat) (a b : Estado), Coincide S d a b → (∀ i, i < k → S (iter R i a).pos) →
      Coincide S d (iter R k a) (iter R k b)
  | 0, _, _, h, _ => h
  | k + 1, a, b, h, hr => by
      simp only [iter]
      apply iter_coincide R k (paso R a) (paso R b) (paso_coincide R h (hr 0 (by omega)))
      intro i hi
      have := hr (i + 1) (by omega)
      simpa [iter] using this

/-- **Lema de repetición.** Si `S` es cerrado bajo `+d`, el primer periodo de la hormiga se queda en `S`,
y tras `P` pasos el estado coincide en `S` con el inicial trasladado por `d`, entonces cada bloque de `P`
pasos coincide con el siguiente, para siempre. -/
theorem repeticion (R : Regla) (s : Estado) (P : Nat) (d : Pt) (S : Pt → Prop)
    (hS : ∀ x, S x → S (x + d))
    (hrun : ∀ i, i < P → S (iter R i s).pos)
    (hc : Coincide S d s (iter R P s)) :
    ∀ q, Coincide S d (iter R (q * P) s) (iter R ((q + 1) * P) s) ∧
         ∀ i, i < P → S (iter R (q * P + i) s).pos := by
  intro q
  induction q with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa [iter] using hc
    · intro i hi; simpa using hrun i hi
  | succ q ih =>
    obtain ⟨hcq, hrq⟩ := ih
    have hrq' : ∀ i, i < P → S (iter R i (iter R (q * P) s)).pos := by
      intro i hi; rw [← iter_add]; exact hrq i hi
    have key : ∀ i, i ≤ P → Coincide S d (iter R i (iter R (q * P) s)) (iter R i (iter R ((q + 1) * P) s)) := by
      intro i hi
      exact iter_coincide R i _ _ hcq (fun j hj => hrq' j (by omega))
    refine ⟨?_, ?_⟩
    · have h := key P (Nat.le_refl P)
      rw [← iter_add, ← iter_add] at h
      rw [show q * P + P = (q + 1) * P by rw [Nat.succ_mul]] at h
      rw [show (q + 1) * P + P = (q + 1 + 1) * P by rw [Nat.succ_mul (q + 1)]] at h
      exact h
    · intro i hi
      have h := (key i (Nat.le_of_lt hi)).1
      rw [← iter_add] at h
      rw [h]
      apply hS
      rw [← iter_add]; exact hrq i hi

/-- Consecuencia: la trayectoria se repite trasladada `q·d` cada `P` pasos (una autopista). -/
def EsAutopista (R : Regla) (s : Estado) (P : Nat) (d : Pt) : Prop :=
  ∀ q i, i < P → (iter R (q * P + i) s).pos = (iter R i s).pos + Pt.smul q d ∧
                 (iter R (q * P + i) s).dir = (iter R i s).dir

theorem smul_succ (q : Nat) (d : Pt) : Pt.smul (q + 1) d = Pt.smul q d + d := by
  apply Pt.ext' <;> simp [Pt.smul, Int.add_mul]

theorem autopista_de_repeticion (R : Regla) (s : Estado) (P : Nat) (d : Pt) (S : Pt → Prop)
    (hS : ∀ x, S x → S (x + d))
    (hrun : ∀ i, i < P → S (iter R i s).pos)
    (hc : Coincide S d s (iter R P s)) : EsAutopista R s P d := by
  have hrep := repeticion R s P d S hS hrun hc
  intro q
  induction q with
  | zero =>
    intro i _
    refine ⟨?_, by simp⟩
    simp only [Nat.zero_mul, Nat.zero_add]
    apply Pt.ext' <;> simp [Pt.smul]
  | succ q ih =>
    intro i hi
    obtain ⟨hcq, hrq⟩ := hrep q
    have hk := iter_coincide R i _ _ hcq (fun j hj => by rw [← iter_add]; exact hrq j (by omega))
    rw [← iter_add, ← iter_add] at hk
    obtain ⟨hp, hd, _⟩ := hk
    obtain ⟨ihp, ihd⟩ := ih i hi
    refine ⟨?_, ?_⟩
    · rw [hp, ihp, smul_succ]
      apply Pt.ext' <;> simp <;> omega
    · rw [hd, ihd]

/-- Una autopista también se repite si se avanza cualquier número de pasos, no solo menos de un periodo. -/
theorem autopista_todo (R : Regla) (s : Estado) (P : Nat) (d : Pt) (h : EsAutopista R s P d) (hP : 0 < P) :
    ∀ q j, (iter R (q * P + j) s).pos = (iter R j s).pos + Pt.smul q d ∧
           (iter R (q * P + j) s).dir = (iter R j s).dir := by
  intro q j
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < P ∧ j = a * P + b :=
    ⟨j / P, j % P, Nat.mod_lt _ hP, by rw [Nat.mul_comm]; exact (Nat.div_add_mod j P).symm⟩
  obtain ⟨h1, h2⟩ := h (q + a) b hb
  obtain ⟨h3, h4⟩ := h a b hb
  rw [show q * P + (a * P + b) = (q + a) * P + b by rw [Nat.add_mul, Nat.add_assoc], h1, h3]
  refine ⟨?_, by rw [h2, h4]⟩
  apply Pt.ext' <;> simp only [Pt.add_x, Pt.add_y, Pt.smul, Int.natCast_add, Int.add_mul] <;> omega

/-- Si P es periodo con deriva d, también lo es 2P con deriva 2d. -/
theorem autopista_doble (R : Regla) (s : Estado) (P : Nat) (d : Pt) (h : EsAutopista R s P d) :
    EsAutopista R s (2 * P) (d + d) := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · intro q i hi; subst hP; simp at hi
  intro q i _
  obtain ⟨h1, h2⟩ := autopista_todo R s P d h hP (2 * q) i
  rw [show q * (2 * P) + i = 2 * q * P + i by rw [Nat.mul_left_comm, ← Nat.mul_assoc]]
  refine ⟨?_, h2⟩
  rw [h1]
  apply Pt.ext' <;> simp only [Pt.add_x, Pt.add_y, Pt.smul, Int.natCast_mul, Int.mul_add, Int.mul_assoc] <;> omega

end Hormiga
