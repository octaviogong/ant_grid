/-
  ARCHIVO GENERADO por prueba/gen_lean.py a partir de los certificados del motor simbólico.
  Teorema: periodo de la autopista de RⁿLᵐ desde el tablero en blanco.
-/
import Hormiga.Simbolico

namespace Hormiga

/-- Certificado compacto: `P k` = k pasos, `M` = marca, `A a b c` = acelerar r = a + b·s + c·t. -/
inductive SegC where
  | P (k : Nat)
  | M
  | A (a b c : Int)

def expand : List SegC → List Seg
  | [] => []
  | SegC.P k :: r => List.replicate k Seg.paso ++ expand r
  | SegC.M :: r => Seg.marca :: expand r
  | SegC.A a b c :: r => Seg.acel ⟨a, b, c⟩ :: expand r

/-- Lo que queremos para (n, j), m = 2j+1: desde el blanco, la autopista empieza a más tardar en el paso
204·(n + m) y tiene periodo 16(n + m) − 20. -/
def Bueno (n j : Nat) : Prop :=
  ∃ t1 : Nat, t1 ≤ 204 * (n + 2 * j + 1) ∧
    ∃ d : Pt, EsAutopista (RL n (2 * j + 1)) (iter (RL n (2 * j + 1)) t1 blanco.toE) (16 * (n + 2 * j + 1) - 20) d

/-- Familia m = 1: transitorio ≤ 40·(n + 1) y periodo 16(n + 1) − 12 = 16n + 4. -/
def BuenoUno (n j : Nat) : Prop :=
  ∃ t1 : Nat, t1 ≤ 40 * (n + 2 * j + 1) ∧
    ∃ d : Pt, EsAutopista (RL n (2 * j + 1)) (iter (RL n (2 * j + 1)) t1 blanco.toE) (16 * (n + 2 * j + 1) - 12) d

theorem toNat_eq {z : Int} {k : Nat} (h : z = k) : z.toNat = k := by subst h; simp

theorem concA_nil (s t : Nat) : (⟨concA [] s t, ⟨0, 0⟩, 0⟩ : Estado) = blanco.toE := by
  apply Estado.ext'
  · funext x; simp [concA, lookA, Aff.ev_k, blanco, EL.toE, look]
  · rfl
  · rfl

def M0 (n j : Nat) : Prop := ((1:Int) ∣ (0 + 1*(n:Int) + -2*(j:Int)) ∧ (1:Int) ∣ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ 0 ≤ (0 + 1*(n:Int) + -2*(j:Int)) ∧ 0 ≤ (-2 + 0*(n:Int) + 1*(j:Int)))
def M1 (n j : Nat) : Prop := ((2:Int) ∣ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-4 + 1*(n:Int) + 0*(j:Int)) = 2*(-2 + 0*(n:Int) + 1*(j:Int))))
def M2 (n j : Nat) : Prop := ((n:Int) = 4 ∧ (j:Int) = 2)
def M3 (n j : Nat) : Prop := ((2:Int) ∣ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-6 + 1*(n:Int) + 0*(j:Int)) = 2*(-3 + 0*(n:Int) + 1*(j:Int))))
def M4 (n j : Nat) : Prop := ((n:Int) = 6 ∧ (j:Int) = 3)
def M5 (n j : Nat) : Prop := ((2:Int) ∣ (-8 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-8 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-8 + 1*(n:Int) + 0*(j:Int)) = 2*(-4 + 0*(n:Int) + 1*(j:Int))))
def M6 (n j : Nat) : Prop := ((n:Int) = 8 ∧ (j:Int) = 4)
def M7 (n j : Nat) : Prop := ((2:Int) ∣ (-10 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-10 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-10 + 1*(n:Int) + 0*(j:Int)) = 2*(-5 + 0*(n:Int) + 1*(j:Int))))
def M8 (n j : Nat) : Prop := ((n:Int) = 10 ∧ (j:Int) = 5)
def M9 (n j : Nat) : Prop := ((2:Int) ∣ (-12 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-12 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-12 + 1*(n:Int) + 0*(j:Int)) = 2*(-6 + 0*(n:Int) + 1*(j:Int))))
def M10 (n j : Nat) : Prop := ((n:Int) = 12 ∧ (j:Int) = 6)
def M11 (n j : Nat) : Prop := ((n:Int) = 14 ∧ (j:Int) = 7)
def M12 (n j : Nat) : Prop := ((n:Int) = 16 ∧ (j:Int) = 8)
def M13 (n j : Nat) : Prop := ((2:Int) ∣ (-18 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-18 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-18 + 1*(n:Int) + 0*(j:Int)) = 2*(-9 + 0*(n:Int) + 1*(j:Int))))
def M14 (n j : Nat) : Prop := ((n:Int) = 18 ∧ (j:Int) = 9)
def M15 (n j : Nat) : Prop := ((2:Int) ∣ (-20 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-20 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-20 + 1*(n:Int) + 0*(j:Int)) = 2*(-10 + 0*(n:Int) + 1*(j:Int))))
def M16 (n j : Nat) : Prop := ((n:Int) = 20 ∧ (j:Int) = 10)
def M17 (n j : Nat) : Prop := ((2:Int) ∣ (-22 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-22 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-22 + 1*(n:Int) + 0*(j:Int)) = 2*(-11 + 0*(n:Int) + 1*(j:Int))))
def M18 (n j : Nat) : Prop := ((n:Int) = 22 ∧ (j:Int) = 11)
def M19 (n j : Nat) : Prop := ((2:Int) ∣ (-24 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-24 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-24 + 1*(n:Int) + 0*(j:Int)) = 2*(-12 + 0*(n:Int) + 1*(j:Int))))
def M20 (n j : Nat) : Prop := ((n:Int) = 24 ∧ (j:Int) = 12)
def M21 (n j : Nat) : Prop := ((2:Int) ∣ (-26 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-26 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-26 + 1*(n:Int) + 0*(j:Int)) = 2*(-13 + 0*(n:Int) + 1*(j:Int))))
def M22 (n j : Nat) : Prop := ((n:Int) = 26 ∧ (j:Int) = 13)
def M23 (n j : Nat) : Prop := ((2:Int) ∣ (-28 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-28 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-28 + 1*(n:Int) + 0*(j:Int)) = 2*(-14 + 0*(n:Int) + 1*(j:Int))))
def M24 (n j : Nat) : Prop := ((6:Int) ∣ (-28 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-28 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-28 + 1*(n:Int) + 0*(j:Int)) = 6*(-14 + 0*(n:Int) + 1*(j:Int))))
def M25 (n j : Nat) : Prop := ((n:Int) = 28 ∧ (j:Int) = 14)
def M26 (n j : Nat) : Prop := ((6:Int) ∣ (-34 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-34 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-34 + 1*(n:Int) + 0*(j:Int)) = 6*(-17 + 0*(n:Int) + 1*(j:Int))))
def M27 (n j : Nat) : Prop := ((n:Int) = 34 ∧ (j:Int) = 17)
def M28 (n j : Nat) : Prop := ((6:Int) ∣ (-40 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-40 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-40 + 1*(n:Int) + 0*(j:Int)) = 6*(-20 + 0*(n:Int) + 1*(j:Int))))
def M29 (n j : Nat) : Prop := ((n:Int) = 40 ∧ (j:Int) = 20)
def M30 (n j : Nat) : Prop := ((6:Int) ∣ (-46 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-46 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-46 + 1*(n:Int) + 0*(j:Int)) = 6*(-23 + 0*(n:Int) + 1*(j:Int))))
def M31 (n j : Nat) : Prop := ((6:Int) ∣ (-30 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-30 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-30 + 1*(n:Int) + 0*(j:Int)) = 6*(-15 + 0*(n:Int) + 1*(j:Int))))
def M32 (n j : Nat) : Prop := ((n:Int) = 30 ∧ (j:Int) = 15)
def M33 (n j : Nat) : Prop := ((6:Int) ∣ (-36 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-36 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-36 + 1*(n:Int) + 0*(j:Int)) = 6*(-18 + 0*(n:Int) + 1*(j:Int))))
def M34 (n j : Nat) : Prop := ((n:Int) = 36 ∧ (j:Int) = 18)
def M35 (n j : Nat) : Prop := ((6:Int) ∣ (-42 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-42 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-42 + 1*(n:Int) + 0*(j:Int)) = 6*(-21 + 0*(n:Int) + 1*(j:Int))))
def M36 (n j : Nat) : Prop := ((n:Int) = 42 ∧ (j:Int) = 21)
def M37 (n j : Nat) : Prop := ((6:Int) ∣ (-48 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-48 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-48 + 1*(n:Int) + 0*(j:Int)) = 6*(-24 + 0*(n:Int) + 1*(j:Int))))
def M38 (n j : Nat) : Prop := ((6:Int) ∣ (-32 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-32 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-32 + 1*(n:Int) + 0*(j:Int)) = 6*(-16 + 0*(n:Int) + 1*(j:Int))))
def M39 (n j : Nat) : Prop := ((n:Int) = 32 ∧ (j:Int) = 16)
def M40 (n j : Nat) : Prop := ((6:Int) ∣ (-38 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-38 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-38 + 1*(n:Int) + 0*(j:Int)) = 6*(-19 + 0*(n:Int) + 1*(j:Int))))
def M41 (n j : Nat) : Prop := ((n:Int) = 38 ∧ (j:Int) = 19)
def M42 (n j : Nat) : Prop := ((6:Int) ∣ (-44 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-44 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-44 + 1*(n:Int) + 0*(j:Int)) = 6*(-22 + 0*(n:Int) + 1*(j:Int))))
def M43 (n j : Nat) : Prop := ((n:Int) = 44 ∧ (j:Int) = 22)
def M44 (n j : Nat) : Prop := ((6:Int) ∣ (-50 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-50 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-50 + 1*(n:Int) + 0*(j:Int)) = 6*(-25 + 0*(n:Int) + 1*(j:Int))))
def M45 (n j : Nat) : Prop := ((1:Int) ∣ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ (1:Int) ∣ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ 0 ≤ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ 0 ≤ (-2 + 0*(n:Int) + 1*(j:Int)))
def M46 (n j : Nat) : Prop := ((1:Int) ∣ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ (1:Int) ∣ (0 + 1*(n:Int) + -3*(j:Int)) ∧ 0 ≤ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ 0 ≤ (0 + 1*(n:Int) + -3*(j:Int)))
def M47 (n j : Nat) : Prop := ((3:Int) ∣ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-6 + 1*(n:Int) + 0*(j:Int)) = 3*(-2 + 0*(n:Int) + 1*(j:Int))))
def M48 (n j : Nat) : Prop := ((1:Int) ∣ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ (1:Int) ∣ (-1 + 1*(n:Int) + -3*(j:Int)) ∧ 0 ≤ (-2 + 0*(n:Int) + 1*(j:Int)) ∧ 0 ≤ (-1 + 1*(n:Int) + -3*(j:Int)))
def M49 (n j : Nat) : Prop := ((1:Int) ∣ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ (1:Int) ∣ (-1 + -1*(n:Int) + 3*(j:Int)) ∧ 0 ≤ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ 0 ≤ (-1 + -1*(n:Int) + 3*(j:Int)))
def M50 (n j : Nat) : Prop := ((1:Int) ∣ (-1 + -1*(n:Int) + 3*(j:Int)) ∧ (1:Int) ∣ (0 + 2*(n:Int) + -5*(j:Int)) ∧ 0 ≤ (-1 + -1*(n:Int) + 3*(j:Int)) ∧ 0 ≤ (0 + 2*(n:Int) + -5*(j:Int)))
def M51 (n j : Nat) : Prop := ((5:Int) ∣ (-5 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-5 + 1*(n:Int) + 0*(j:Int)) ∧ (2*(-5 + 1*(n:Int) + 0*(j:Int)) = 5*(-2 + 0*(n:Int) + 1*(j:Int))))
def M52 (n j : Nat) : Prop := ((n:Int) = 5 ∧ (j:Int) = 2)
def M53 (n j : Nat) : Prop := ((5:Int) ∣ (-10 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-10 + 1*(n:Int) + 0*(j:Int)) ∧ (2*(-10 + 1*(n:Int) + 0*(j:Int)) = 5*(-4 + 0*(n:Int) + 1*(j:Int))))
def M54 (n j : Nat) : Prop := ((1:Int) ∣ (-1 + -1*(n:Int) + 3*(j:Int)) ∧ (1:Int) ∣ (-1 + 2*(n:Int) + -5*(j:Int)) ∧ 0 ≤ (-1 + -1*(n:Int) + 3*(j:Int)) ∧ 0 ≤ (-1 + 2*(n:Int) + -5*(j:Int)))
def M55 (n j : Nat) : Prop := ((1:Int) ∣ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ (1:Int) ∣ (-1 + -2*(n:Int) + 5*(j:Int)) ∧ 0 ≤ (-1 + 1*(n:Int) + -2*(j:Int)) ∧ 0 ≤ (-1 + -2*(n:Int) + 5*(j:Int)))
def M56 (n j : Nat) : Prop := ((2:Int) ∣ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ (1*(-7 + 1*(n:Int) + 0*(j:Int)) = 2*(-3 + 0*(n:Int) + 1*(j:Int))))
def M57 (n j : Nat) : Prop := ((6:Int) ∣ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-7 + 1*(n:Int) + 0*(j:Int)) = 6*(-3 + 0*(n:Int) + 1*(j:Int))))
def M58 (n j : Nat) : Prop := ((6:Int) ∣ (-9 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-9 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-9 + 1*(n:Int) + 0*(j:Int)) = 6*(-4 + 0*(n:Int) + 1*(j:Int))))
def M59 (n j : Nat) : Prop := ((6:Int) ∣ (-11 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-11 + 1*(n:Int) + 0*(j:Int)) ∧ (3*(-11 + 1*(n:Int) + 0*(j:Int)) = 6*(-5 + 0*(n:Int) + 1*(j:Int))))
def M60 (n j : Nat) : Prop := ((1:Int) ∣ (-2 + 1*(n:Int) + -2*(j:Int)) ∧ (1:Int) ∣ (-1 + -2*(n:Int) + 5*(j:Int)) ∧ 0 ≤ (-2 + 1*(n:Int) + -2*(j:Int)) ∧ 0 ≤ (-1 + -2*(n:Int) + 5*(j:Int)))
def M61 (n j : Nat) : Prop := ((1:Int) ∣ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-3 + 1*(n:Int) + 0*(j:Int)) = 1*(-1 + 0*(n:Int) + 1*(j:Int))))
def M62 (n j : Nat) : Prop := ((2:Int) ∣ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-3 + 1*(n:Int) + 0*(j:Int)) = 2*(-1 + 0*(n:Int) + 1*(j:Int))))
def M63 (n j : Nat) : Prop := ((6:Int) ∣ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-3 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M64 (n j : Nat) : Prop := ((n:Int) = 3 ∧ (j:Int) = 1)
def M65 (n j : Nat) : Prop := ((6:Int) ∣ (-9 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-9 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-9 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M66 (n j : Nat) : Prop := ((6:Int) ∣ (-5 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-5 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-5 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M67 (n j : Nat) : Prop := ((6:Int) ∣ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-7 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-7 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M68 (n j : Nat) : Prop := ((2:Int) ∣ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-4 + 1*(n:Int) + 0*(j:Int)) = 2*(-1 + 0*(n:Int) + 1*(j:Int))))
def M69 (n j : Nat) : Prop := ((6:Int) ∣ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-4 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M70 (n j : Nat) : Prop := ((6:Int) ∣ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-6 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-6 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M71 (n j : Nat) : Prop := ((6:Int) ∣ (-8 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-8 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-8 + 1*(n:Int) + 0*(j:Int)) = 6*(-1 + 0*(n:Int) + 1*(j:Int))))
def M72 (n j : Nat) : Prop := ((1:Int) ∣ (-2 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-2 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-2 + 1*(n:Int) + 0*(j:Int)) = 1*(0 + 0*(n:Int) + 1*(j:Int))))
def M73 (n j : Nat) : Prop := ((2:Int) ∣ (-2 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-2 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-2 + 1*(n:Int) + 0*(j:Int)) = 2*(0 + 0*(n:Int) + 1*(j:Int))))
def M74 (n j : Nat) : Prop := ((n:Int) = 2 ∧ (j:Int) = 0)
def M75 (n j : Nat) : Prop := ((2:Int) ∣ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-4 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-4 + 1*(n:Int) + 0*(j:Int)) = 2*(0 + 0*(n:Int) + 1*(j:Int))))
def M76 (n j : Nat) : Prop := ((2:Int) ∣ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ 0 ≤ (-3 + 1*(n:Int) + 0*(j:Int)) ∧ (0*(-3 + 1*(n:Int) + 0*(j:Int)) = 2*(0 + 0*(n:Int) + 1*(j:Int))))

def C2 : Cono := ⟨⟨4, 0, 0⟩, ⟨2, 0, 0⟩⟩
def pre2 : List SegC := [SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 20, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 38, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 38, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 212, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 67]
def per2 : List SegC := [SegC.P 3, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 51]
theorem cert2 : verificaS C2 [] 0 (expand pre2) (expand per2) ⟨-1, 1⟩ (6) = some (⟨522, 0, 0⟩, ⟨62, 0, 0⟩) := by native_decide
theorem bueno2 (n j : Nat) (h : M2 n j) : Bueno n j := by
  unfold M2 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C2 [] 0 _ _ _ _ _ _ cert2 0 0
  have hn : C2.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C2, Aff.ev, ]; omega
  have hm : C2.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C2, Aff.ev, ]; omega
  have hP : 2 * (Aff.ev ⟨62, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨522, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key⟩

def C4 : Cono := ⟨⟨6, 0, 0⟩, ⟨3, 0, 0⟩⟩
def pre4 : List SegC := [SegC.M, SegC.P 4, SegC.A (5) (0) (0), SegC.M, SegC.P 20, SegC.A (2) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (1) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 24, SegC.A (1) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 24, SegC.A (1) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 54, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 32, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 57, SegC.M, SegC.P 12, SegC.A (1) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 27, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 160, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 107, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 174, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 70]
def per4 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 54, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 66]
theorem cert4 : verificaS C4 [] 0 (expand pre4) (expand per4) ⟨-2, 2⟩ (18) = some (⟨1565, 0, 0⟩, ⟨188, 0, 0⟩) := by native_decide
theorem bueno4 (n j : Nat) (h : M4 n j) : Bueno n j := by
  unfold M4 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C4 [] 0 _ _ _ _ _ _ cert4 0 0
  have hn : C4.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C4, Aff.ev, ]; omega
  have hm : C4.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C4, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨188, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨1565, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C6 : Cono := ⟨⟨8, 0, 0⟩, ⟨4, 0, 0⟩⟩
def pre6 : List SegC := [SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 20, SegC.A (3) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 24, SegC.A (2) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 24, SegC.A (2) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 42, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 38, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 53, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 93, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 106, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 28, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 132, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 54, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 26, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 50, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 114, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 77, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (1) (0) (0), SegC.P 30]
def per6 : List SegC := [SegC.P 3, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (1) (0) (0), SegC.P 30]
theorem cert6 : verificaS C6 [] 0 (expand pre6) (expand per6) ⟨-2, 2⟩ (20) = some (⟨2658, 0, 0⟩, ⟨252, 0, 0⟩) := by native_decide
theorem bueno6 (n j : Nat) (h : M6 n j) : Bueno n j := by
  unfold M6 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C6 [] 0 _ _ _ _ _ _ cert6 0 0
  have hn : C6.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C6, Aff.ev, ]; omega
  have hm : C6.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C6, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨252, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨2658, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C8 : Cono := ⟨⟨10, 0, 0⟩, ⟨5, 0, 0⟩⟩
def pre8 : List SegC := [SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 20, SegC.A (4) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (3) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 24, SegC.A (3) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 24, SegC.A (3) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (1) (0) (0), SegC.P 41, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 66, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 215, SegC.M, SegC.P 12, SegC.A (3) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.P 53, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 65, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 75, SegC.M, SegC.P 40, SegC.A (1) (0) (0), SegC.P 100, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 61, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 12, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 108, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (2) (0) (0), SegC.P 21]
def per8 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (2) (0) (0), SegC.P 21]
theorem cert8 : verificaS C8 [] 0 (expand pre8) (expand per8) ⟨-2, -2⟩ (16) = some (⟨2736, 0, 0⟩, ⟨316, 0, 0⟩) := by native_decide
theorem bueno8 (n j : Nat) (h : M8 n j) : Bueno n j := by
  unfold M8 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C8 [] 0 _ _ _ _ _ _ cert8 0 0
  have hn : C8.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C8, Aff.ev, ]; omega
  have hm : C8.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C8, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨316, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨2736, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C11 : Cono := ⟨⟨14, 0, 0⟩, ⟨7, 0, 0⟩⟩
def pre11 : List SegC := [SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 20, SegC.A (6) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (5) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 24, SegC.A (5) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 24, SegC.A (5) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (3) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (1) (0) (0), SegC.P 186, SegC.M, SegC.P 12, SegC.A (5) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (5) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (1) (0) (0), SegC.P 114, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 93, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 50, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 135, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.P 49, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 92, SegC.M, SegC.P 12, SegC.A (1) (0) (0), SegC.P 5, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 29, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 20, SegC.A (1) (0) (0), SegC.P 33, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 38, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 301, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.P 12, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 72, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.M, SegC.P 24, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.M, SegC.P 12, SegC.A (1) (0) (0), SegC.P 105, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 28, SegC.M, SegC.P 12, SegC.A (1) (0) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 122, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 66, SegC.M, SegC.P 20, SegC.A (1) (0) (0), SegC.P 162, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 54, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 95, SegC.M, SegC.P 4, SegC.A (3) (0) (0), SegC.P 42, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.M, SegC.P 20, SegC.A (2) (0) (0), SegC.P 25, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 1]
def per11 : List SegC := [SegC.P 3, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.M, SegC.P 20, SegC.A (2) (0) (0), SegC.P 5, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 5, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.M, SegC.P 20, SegC.A (2) (0) (0), SegC.P 25, SegC.M, SegC.P 12, SegC.A (2) (0) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 1]
theorem cert11 : verificaS C11 [] 0 (expand pre11) (expand per11) ⟨2, -2⟩ (40) = some (⟨5888, 0, 0⟩, ⟨444, 0, 0⟩) := by native_decide
theorem bueno11 (n j : Nat) (h : M11 n j) : Bueno n j := by
  unfold M11 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C11 [] 0 _ _ _ _ _ _ cert11 0 0
  have hn : C11.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C11, Aff.ev, ]; omega
  have hm : C11.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C11, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨444, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨5888, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C12 : Cono := ⟨⟨16, 0, 0⟩, ⟨8, 0, 0⟩⟩
def pre12 : List SegC := [SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 20, SegC.A (7) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (6) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 24, SegC.A (6) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 24, SegC.A (6) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (4) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 114, SegC.M, SegC.P 12, SegC.A (6) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (6) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (3) (0) (0), SegC.P 257, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 137, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (5) (0) (0), SegC.P 21]
def per12 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (5) (0) (0), SegC.P 21]
theorem cert12 : verificaS C12 [] 0 (expand pre12) (expand per12) ⟨-2, -2⟩ (16) = some (⟨3692, 0, 0⟩, ⟨508, 0, 0⟩) := by native_decide
theorem bueno12 (n j : Nat) (h : M12 n j) : Bueno n j := by
  unfold M12 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C12 [] 0 _ _ _ _ _ _ cert12 0 0
  have hn : C12.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C12, Aff.ev, ]; omega
  have hm : C12.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C12, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨508, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨3692, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C14 : Cono := ⟨⟨18, 0, 0⟩, ⟨9, 0, 0⟩⟩
def pre14 : List SegC := [SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 20, SegC.A (8) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (7) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 24, SegC.A (7) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 24, SegC.A (7) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (5) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 82, SegC.M, SegC.P 12, SegC.A (7) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (7) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (4) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 209, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 181, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (6) (0) (0), SegC.P 21]
def per14 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (6) (0) (0), SegC.P 21]
theorem cert14 : verificaS C14 [] 0 (expand pre14) (expand per14) ⟨-2, -2⟩ (16) = some (⟨4132, 0, 0⟩, ⟨572, 0, 0⟩) := by native_decide
theorem bueno14 (n j : Nat) (h : M14 n j) : Bueno n j := by
  unfold M14 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C14 [] 0 _ _ _ _ _ _ cert14 0 0
  have hn : C14.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C14, Aff.ev, ]; omega
  have hm : C14.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C14, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨572, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨4132, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C16 : Cono := ⟨⟨20, 0, 0⟩, ⟨10, 0, 0⟩⟩
def pre16 : List SegC := [SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 20, SegC.A (9) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (8) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 24, SegC.A (8) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 24, SegC.A (8) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (6) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (8) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (8) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (5) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (2) (0) (0), SegC.P 154, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 241, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 76, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (7) (0) (0), SegC.P 21]
def per16 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (7) (0) (0), SegC.P 21]
theorem cert16 : verificaS C16 [] 0 (expand pre16) (expand per16) ⟨-2, -2⟩ (16) = some (⟨4624, 0, 0⟩, ⟨636, 0, 0⟩) := by native_decide
theorem bueno16 (n j : Nat) (h : M16 n j) : Bueno n j := by
  unfold M16 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C16 [] 0 _ _ _ _ _ _ cert16 0 0
  have hn : C16.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C16, Aff.ev, ]; omega
  have hm : C16.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C16, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨636, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨4624, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C18 : Cono := ⟨⟨22, 0, 0⟩, ⟨11, 0, 0⟩⟩
def pre18 : List SegC := [SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 20, SegC.A (10) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (9) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 24, SegC.A (9) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 24, SegC.A (9) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (7) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (9) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (9) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (6) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (3) (0) (0), SegC.P 214, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 212, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 57, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 49, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (8) (0) (0), SegC.P 21]
def per18 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (8) (0) (0), SegC.P 21]
theorem cert18 : verificaS C18 [] 0 (expand pre18) (expand per18) ⟨-2, -2⟩ (16) = some (⟨5060, 0, 0⟩, ⟨700, 0, 0⟩) := by native_decide
theorem bueno18 (n j : Nat) (h : M18 n j) : Bueno n j := by
  unfold M18 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C18 [] 0 _ _ _ _ _ _ cert18 0 0
  have hn : C18.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C18, Aff.ev, ]; omega
  have hm : C18.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C18, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨700, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨5060, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C20 : Cono := ⟨⟨24, 0, 0⟩, ⟨12, 0, 0⟩⟩
def pre20 : List SegC := [SegC.M, SegC.P 4, SegC.A (23) (0) (0), SegC.M, SegC.P 20, SegC.A (11) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (10) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 24, SegC.A (10) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 24, SegC.A (10) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (8) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (10) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (10) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (7) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (4) (0) (0), SegC.P 186, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 241, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 48, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (9) (0) (0), SegC.P 21]
def per20 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (9) (0) (0), SegC.P 21]
theorem cert20 : verificaS C20 [] 0 (expand pre20) (expand per20) ⟨-2, -2⟩ (16) = some (⟨5420, 0, 0⟩, ⟨764, 0, 0⟩) := by native_decide
theorem bueno20 (n j : Nat) (h : M20 n j) : Bueno n j := by
  unfold M20 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C20 [] 0 _ _ _ _ _ _ cert20 0 0
  have hn : C20.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C20, Aff.ev, ]; omega
  have hm : C20.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C20, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨764, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨5420, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C22 : Cono := ⟨⟨26, 0, 0⟩, ⟨13, 0, 0⟩⟩
def pre22 : List SegC := [SegC.M, SegC.P 4, SegC.A (25) (0) (0), SegC.M, SegC.P 20, SegC.A (12) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (11) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 24, SegC.A (11) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 24, SegC.A (11) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (22) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (9) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (11) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (11) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (8) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (5) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 241, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 48, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (10) (0) (0), SegC.P 21]
def per22 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (10) (0) (0), SegC.P 21]
theorem cert22 : verificaS C22 [] 0 (expand pre22) (expand per22) ⟨-2, -2⟩ (16) = some (⟨5796, 0, 0⟩, ⟨828, 0, 0⟩) := by native_decide
theorem bueno22 (n j : Nat) (h : M22 n j) : Bueno n j := by
  unfold M22 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C22 [] 0 _ _ _ _ _ _ cert22 0 0
  have hn : C22.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C22, Aff.ev, ]; omega
  have hm : C22.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C22, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨828, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨5796, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C25 : Cono := ⟨⟨28, 0, 0⟩, ⟨14, 0, 0⟩⟩
def pre25 : List SegC := [SegC.M, SegC.P 4, SegC.A (27) (0) (0), SegC.M, SegC.P 20, SegC.A (13) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (12) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 24, SegC.A (12) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 24, SegC.A (12) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (24) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (10) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (12) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (12) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (9) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (6) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (2) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 205, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 48, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (11) (0) (0), SegC.P 21]
def per25 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (11) (0) (0), SegC.P 21]
theorem cert25 : verificaS C25 [] 0 (expand pre25) (expand per25) ⟨-2, -2⟩ (16) = some (⟨6172, 0, 0⟩, ⟨892, 0, 0⟩) := by native_decide
theorem bueno25 (n j : Nat) (h : M25 n j) : Bueno n j := by
  unfold M25 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C25 [] 0 _ _ _ _ _ _ cert25 0 0
  have hn : C25.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C25, Aff.ev, ]; omega
  have hm : C25.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C25, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨892, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨6172, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C27 : Cono := ⟨⟨34, 0, 0⟩, ⟨17, 0, 0⟩⟩
def pre27 : List SegC := [SegC.M, SegC.P 4, SegC.A (33) (0) (0), SegC.M, SegC.P 20, SegC.A (16) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (15) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 24, SegC.A (15) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 24, SegC.A (15) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (30) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (13) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (15) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (12) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (9) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 140, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (14) (0) (0), SegC.P 21]
def per27 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (14) (0) (0), SegC.P 21]
theorem cert27 : verificaS C27 [] 0 (expand pre27) (expand per27) ⟨-2, -2⟩ (16) = some (⟨7448, 0, 0⟩, ⟨1084, 0, 0⟩) := by native_decide
theorem bueno27 (n j : Nat) (h : M27 n j) : Bueno n j := by
  unfold M27 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C27 [] 0 _ _ _ _ _ _ cert27 0 0
  have hn : C27.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C27, Aff.ev, ]; omega
  have hm : C27.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C27, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1084, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨7448, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C29 : Cono := ⟨⟨40, 0, 0⟩, ⟨20, 0, 0⟩⟩
def pre29 : List SegC := [SegC.M, SegC.P 4, SegC.A (39) (0) (0), SegC.M, SegC.P 20, SegC.A (19) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (18) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 24, SegC.A (18) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 24, SegC.A (18) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (36) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (16) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (18) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (15) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (12) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (8) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (17) (0) (0), SegC.P 21]
def per29 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (17) (0) (0), SegC.P 21]
theorem cert29 : verificaS C29 [] 0 (expand pre29) (expand per29) ⟨-2, -2⟩ (16) = some (⟨8772, 0, 0⟩, ⟨1276, 0, 0⟩) := by native_decide
theorem bueno29 (n j : Nat) (h : M29 n j) : Bueno n j := by
  unfold M29 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C29 [] 0 _ _ _ _ _ _ cert29 0 0
  have hn : C29.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C29, Aff.ev, ]; omega
  have hm : C29.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C29, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1276, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨8772, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C30 : Cono := ⟨⟨46, 0, 6⟩, ⟨23, 0, 3⟩⟩
def pre30 : List SegC := [SegC.M, SegC.P 4, SegC.A (45) (0) (6), SegC.M, SegC.P 20, SegC.A (22) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 6, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (21) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 24, SegC.A (21) (0) (3), SegC.P 14, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 24, SegC.A (21) (0) (3), SegC.P 64, SegC.M, SegC.P 4, SegC.A (42) (0) (6), SegC.P 34, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 30, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 1, SegC.M, SegC.P 28, SegC.A (19) (0) (3), SegC.P 33, SegC.M, SegC.P 8, SegC.A (17) (0) (3), SegC.P 8, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (17) (0) (3), SegC.P 29, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (20) (0) (3), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (21) (0) (3), SegC.P 31, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 3, SegC.M, SegC.P 4, SegC.A (21) (0) (3), SegC.P 14, SegC.M, SegC.P 32, SegC.A (18) (0) (3), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (15) (0) (3), SegC.P 17, SegC.M, SegC.P 8, SegC.A (11) (0) (3), SegC.P 125, SegC.M, SegC.P 8, SegC.A (17) (0) (3), SegC.P 18, SegC.M, SegC.P 8, SegC.A (19) (0) (3), SegC.P 169, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (21) (0) (3), SegC.P 25, SegC.M, SegC.P 8, SegC.A (20) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (4) (0) (3), SegC.P 37, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (20) (0) (3), SegC.P 21]
def per30 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.M, SegC.P 16, SegC.A (21) (0) (3), SegC.P 21, SegC.M, SegC.P 8, SegC.A (20) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (20) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (20) (0) (3), SegC.P 21]
theorem cert30 : verificaS C30 [] 0 (expand pre30) (expand per30) ⟨-2, -2⟩ (16) = some (⟨10080, 0, 1308⟩, ⟨1468, 0, 192⟩) := by native_decide
theorem bueno30 (n j : Nat) (h : M30 n j) : Bueno n j := by
  unfold M30 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C30 [] 0 _ _ _ _ _ _ cert30 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C30.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C30, Aff.ev, hqn, ]; omega
  have hm : C30.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C30, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨1468, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨10080, 0, 1308⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C32 : Cono := ⟨⟨30, 0, 0⟩, ⟨15, 0, 0⟩⟩
def pre32 : List SegC := [SegC.M, SegC.P 4, SegC.A (29) (0) (0), SegC.M, SegC.P 20, SegC.A (14) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (13) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 24, SegC.A (13) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 24, SegC.A (13) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (26) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (11) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (13) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (13) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (10) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (7) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (3) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (11) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 48, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (12) (0) (0), SegC.P 21]
def per32 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (12) (0) (0), SegC.P 21]
theorem cert32 : verificaS C32 [] 0 (expand pre32) (expand per32) ⟨-2, -2⟩ (16) = some (⟨6548, 0, 0⟩, ⟨956, 0, 0⟩) := by native_decide
theorem bueno32 (n j : Nat) (h : M32 n j) : Bueno n j := by
  unfold M32 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C32 [] 0 _ _ _ _ _ _ cert32 0 0
  have hn : C32.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C32, Aff.ev, ]; omega
  have hm : C32.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C32, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨956, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨6548, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C34 : Cono := ⟨⟨36, 0, 0⟩, ⟨18, 0, 0⟩⟩
def pre34 : List SegC := [SegC.M, SegC.P 4, SegC.A (35) (0) (0), SegC.M, SegC.P 20, SegC.A (17) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (16) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 24, SegC.A (16) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 24, SegC.A (16) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (32) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (14) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (16) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (16) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (13) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (10) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (6) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 72, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (15) (0) (0), SegC.P 21]
def per34 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.M, SegC.P 16, SegC.A (16) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (15) (0) (0), SegC.P 21]
theorem cert34 : verificaS C34 [] 0 (expand pre34) (expand per34) ⟨-2, -2⟩ (16) = some (⟨7900, 0, 0⟩, ⟨1148, 0, 0⟩) := by native_decide
theorem bueno34 (n j : Nat) (h : M34 n j) : Bueno n j := by
  unfold M34 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C34 [] 0 _ _ _ _ _ _ cert34 0 0
  have hn : C34.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C34, Aff.ev, ]; omega
  have hm : C34.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C34, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1148, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨7900, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C36 : Cono := ⟨⟨42, 0, 0⟩, ⟨21, 0, 0⟩⟩
def pre36 : List SegC := [SegC.M, SegC.P 4, SegC.A (41) (0) (0), SegC.M, SegC.P 20, SegC.A (20) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (19) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 24, SegC.A (19) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 24, SegC.A (19) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (38) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (17) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (19) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (19) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (16) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (13) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (9) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 37, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (18) (0) (0), SegC.P 21]
def per36 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.M, SegC.P 16, SegC.A (19) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (18) (0) (0), SegC.P 21]
theorem cert36 : verificaS C36 [] 0 (expand pre36) (expand per36) ⟨-2, -2⟩ (16) = some (⟨9208, 0, 0⟩, ⟨1340, 0, 0⟩) := by native_decide
theorem bueno36 (n j : Nat) (h : M36 n j) : Bueno n j := by
  unfold M36 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C36 [] 0 _ _ _ _ _ _ cert36 0 0
  have hn : C36.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C36, Aff.ev, ]; omega
  have hm : C36.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C36, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1340, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨9208, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C37 : Cono := ⟨⟨48, 0, 6⟩, ⟨24, 0, 3⟩⟩
def pre37 : List SegC := [SegC.M, SegC.P 4, SegC.A (47) (0) (6), SegC.M, SegC.P 20, SegC.A (23) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 6, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (22) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 24, SegC.A (22) (0) (3), SegC.P 14, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 24, SegC.A (22) (0) (3), SegC.P 64, SegC.M, SegC.P 4, SegC.A (44) (0) (6), SegC.P 34, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 30, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 1, SegC.M, SegC.P 28, SegC.A (20) (0) (3), SegC.P 33, SegC.M, SegC.P 8, SegC.A (18) (0) (3), SegC.P 8, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (18) (0) (3), SegC.P 29, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (22) (0) (3), SegC.P 31, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 3, SegC.M, SegC.P 4, SegC.A (22) (0) (3), SegC.P 14, SegC.M, SegC.P 32, SegC.A (19) (0) (3), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (16) (0) (3), SegC.P 17, SegC.M, SegC.P 8, SegC.A (12) (0) (3), SegC.P 125, SegC.M, SegC.P 8, SegC.A (18) (0) (3), SegC.P 18, SegC.M, SegC.P 8, SegC.A (20) (0) (3), SegC.P 169, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 25, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (5) (0) (3), SegC.P 37, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (21) (0) (3), SegC.P 21]
def per37 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.M, SegC.P 16, SegC.A (22) (0) (3), SegC.P 21, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (21) (0) (3), SegC.P 21]
theorem cert37 : verificaS C37 [] 0 (expand pre37) (expand per37) ⟨-2, -2⟩ (16) = some (⟨10516, 0, 1308⟩, ⟨1532, 0, 192⟩) := by native_decide
theorem bueno37 (n j : Nat) (h : M37 n j) : Bueno n j := by
  unfold M37 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C37 [] 0 _ _ _ _ _ _ cert37 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C37.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C37, Aff.ev, hqn, ]; omega
  have hm : C37.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C37, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨1532, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨10516, 0, 1308⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C39 : Cono := ⟨⟨32, 0, 0⟩, ⟨16, 0, 0⟩⟩
def pre39 : List SegC := [SegC.M, SegC.P 4, SegC.A (31) (0) (0), SegC.M, SegC.P 20, SegC.A (15) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (14) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 24, SegC.A (14) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 24, SegC.A (14) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (28) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (15) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (12) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (14) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (14) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (14) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (11) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (8) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (4) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (12) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 92, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (13) (0) (0), SegC.P 21]
def per39 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (15) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (13) (0) (0), SegC.P 21]
theorem cert39 : verificaS C39 [] 0 (expand pre39) (expand per39) ⟨-2, -2⟩ (16) = some (⟨6996, 0, 0⟩, ⟨1020, 0, 0⟩) := by native_decide
theorem bueno39 (n j : Nat) (h : M39 n j) : Bueno n j := by
  unfold M39 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C39 [] 0 _ _ _ _ _ _ cert39 0 0
  have hn : C39.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C39, Aff.ev, ]; omega
  have hm : C39.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C39, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1020, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨6996, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C41 : Cono := ⟨⟨38, 0, 0⟩, ⟨19, 0, 0⟩⟩
def pre41 : List SegC := [SegC.M, SegC.P 4, SegC.A (37) (0) (0), SegC.M, SegC.P 20, SegC.A (18) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (17) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 24, SegC.A (17) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 24, SegC.A (17) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (34) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (18) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (15) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (17) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (17) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (17) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (14) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (11) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (7) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (13) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (15) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 104, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (16) (0) (0), SegC.P 21]
def per41 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.M, SegC.P 16, SegC.A (17) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (18) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (16) (0) (0), SegC.P 21]
theorem cert41 : verificaS C41 [] 0 (expand pre41) (expand per41) ⟨-2, -2⟩ (16) = some (⟨8336, 0, 0⟩, ⟨1212, 0, 0⟩) := by native_decide
theorem bueno41 (n j : Nat) (h : M41 n j) : Bueno n j := by
  unfold M41 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C41 [] 0 _ _ _ _ _ _ cert41 0 0
  have hn : C41.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C41, Aff.ev, ]; omega
  have hm : C41.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C41, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1212, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨8336, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C43 : Cono := ⟨⟨44, 0, 0⟩, ⟨22, 0, 0⟩⟩
def pre43 : List SegC := [SegC.M, SegC.P 4, SegC.A (43) (0) (0), SegC.M, SegC.P 20, SegC.A (21) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (21) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (21) (0) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (20) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (20) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 24, SegC.A (20) (0) (0), SegC.P 14, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 24, SegC.A (20) (0) (0), SegC.P 64, SegC.M, SegC.P 4, SegC.A (40) (0) (0), SegC.P 34, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (21) (0) (0), SegC.P 30, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (21) (0) (0), SegC.P 1, SegC.M, SegC.P 28, SegC.A (18) (0) (0), SegC.P 33, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 8, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 29, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (20) (0) (0), SegC.P 31, SegC.M, SegC.P 8, SegC.A (20) (0) (0), SegC.P 3, SegC.M, SegC.P 4, SegC.A (20) (0) (0), SegC.P 14, SegC.M, SegC.P 32, SegC.A (17) (0) (0), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (14) (0) (0), SegC.P 17, SegC.M, SegC.P 8, SegC.A (10) (0) (0), SegC.P 125, SegC.M, SegC.P 8, SegC.A (16) (0) (0), SegC.P 18, SegC.M, SegC.P 8, SegC.A (18) (0) (0), SegC.P 169, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 25, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (3) (0) (0), SegC.P 37, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (19) (0) (0), SegC.P 21]
def per43 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.M, SegC.P 16, SegC.A (20) (0) (0), SegC.P 21, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (19) (0) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (21) (0) (0), SegC.P 21, SegC.M, SegC.P 24, SegC.A (19) (0) (0), SegC.P 21]
theorem cert43 : verificaS C43 [] 0 (expand pre43) (expand per43) ⟨-2, -2⟩ (16) = some (⟨9644, 0, 0⟩, ⟨1404, 0, 0⟩) := by native_decide
theorem bueno43 (n j : Nat) (h : M43 n j) : Bueno n j := by
  unfold M43 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C43 [] 0 _ _ _ _ _ _ cert43 0 0
  have hn : C43.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C43, Aff.ev, ]; omega
  have hm : C43.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C43, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨1404, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨9644, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C44 : Cono := ⟨⟨50, 0, 6⟩, ⟨25, 0, 3⟩⟩
def pre44 : List SegC := [SegC.M, SegC.P 4, SegC.A (49) (0) (6), SegC.M, SegC.P 20, SegC.A (24) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (24) (0) (3), SegC.P 6, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (24) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (23) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (23) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 24, SegC.A (23) (0) (3), SegC.P 14, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 24, SegC.A (23) (0) (3), SegC.P 64, SegC.M, SegC.P 4, SegC.A (46) (0) (6), SegC.P 34, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (24) (0) (3), SegC.P 30, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (24) (0) (3), SegC.P 1, SegC.M, SegC.P 28, SegC.A (21) (0) (3), SegC.P 33, SegC.M, SegC.P 8, SegC.A (19) (0) (3), SegC.P 8, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 37, SegC.M, SegC.P 8, SegC.A (19) (0) (3), SegC.P 29, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 22, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 57, SegC.M, SegC.P 32, SegC.A (2) (0) (0), SegC.P 66, SegC.M, SegC.P 12, SegC.A (23) (0) (3), SegC.P 31, SegC.M, SegC.P 8, SegC.A (23) (0) (3), SegC.P 3, SegC.M, SegC.P 4, SegC.A (23) (0) (3), SegC.P 14, SegC.M, SegC.P 32, SegC.A (20) (0) (3), SegC.M, SegC.P 44, SegC.A (1) (0) (0), SegC.P 23, SegC.M, SegC.P 16, SegC.A (17) (0) (3), SegC.P 17, SegC.M, SegC.P 8, SegC.A (13) (0) (3), SegC.P 125, SegC.M, SegC.P 8, SegC.A (19) (0) (3), SegC.P 18, SegC.M, SegC.P 8, SegC.A (21) (0) (3), SegC.P 169, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 25, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (5) (0) (0), SegC.P 20, SegC.M, SegC.P 48, SegC.A (1) (0) (0), SegC.P 35, SegC.M, SegC.P 32, SegC.A (6) (0) (3), SegC.P 37, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (22) (0) (3), SegC.P 21]
def per44 : List SegC := [SegC.P 12, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.M, SegC.P 16, SegC.A (23) (0) (3), SegC.P 21, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (22) (0) (3), SegC.P 4, SegC.M, SegC.P 4, SegC.A (24) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (22) (0) (3), SegC.P 21]
theorem cert44 : verificaS C44 [] 0 (expand pre44) (expand per44) ⟨-2, -2⟩ (16) = some (⟨10952, 0, 1308⟩, ⟨1596, 0, 192⟩) := by native_decide
theorem bueno44 (n j : Nat) (h : M44 n j) : Bueno n j := by
  unfold M44 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C44 [] 0 _ _ _ _ _ _ cert44 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C44.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C44, Aff.ev, hqn, ]; omega
  have hm : C44.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C44, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨1596, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨10952, 0, 1308⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C47 : Cono := ⟨⟨6, 3, 0⟩, ⟨2, 1, 0⟩⟩
def pre47 : List SegC := [SegC.M, SegC.P 4, SegC.A (5) (3) (0), SegC.M, SegC.P 20, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (1) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (0) (1) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (0) (1) (0)]
def per47 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (1) (0)]
theorem cert47 : verificaS C47 [] 0 (expand pre47) (expand per47) ⟨-1, 1⟩ (1) = some (⟨209, 104, 0⟩, ⟨78, 40, 0⟩) := by native_decide
theorem bueno47 (n j : Nat) (h : M47 n j) : Bueno n j := by
  unfold M47 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C47 [] 0 _ _ _ _ _ _ cert47 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C47.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C47, Aff.ev, hqn, ]; omega
  have hm : C47.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C47, Aff.ev, hqn, ]; omega
  have hP : 2 * (Aff.ev ⟨78, 40, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨209, 104, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key⟩

def C48 : Cono := ⟨⟨7, 3, 1⟩, ⟨2, 1, 0⟩⟩
def pre48 : List SegC := [SegC.M, SegC.P 4, SegC.A (6) (3) (1), SegC.M, SegC.P 20, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (4) (2) (1), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (1) (1), SegC.P 5, SegC.M, SegC.P 4, SegC.A (4) (2) (1), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (0) (1) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (0) (1) (0)]
def per48 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (2) (1), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (0) (0) (1), SegC.M, SegC.P 8, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (0) (0) (1), SegC.M, SegC.P 8, SegC.A (0) (1) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (2) (1), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (1) (0)]
theorem cert48 : verificaS C48 [] 0 (expand pre48) (expand per48) ⟨-2, 2⟩ (2) = some (⟨225, 104, 16⟩, ⟨172, 80, 16⟩) := by native_decide
theorem bueno48 (n j : Nat) (h : M48 n j) : Bueno n j := by
  unfold M48 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have key := verificaS_ok C48 [] 0 _ _ _ _ _ _ cert48 q1.toNat q2.toNat
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have hn : C48.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C48, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C48.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C48, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨172, 80, 16⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨225, 104, 16⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C52 : Cono := ⟨⟨5, 0, 0⟩, ⟨2, 0, 0⟩⟩
def pre52 : List SegC := [SegC.M, SegC.P 4, SegC.A (4) (0) (0), SegC.M, SegC.P 20, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 30]
def per52 : List SegC := [SegC.P 8, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 54, SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.M, SegC.P 16, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (0) (0), SegC.P 5]
theorem cert52 : verificaS C52 [] 0 (expand pre52) (expand per52) ⟨-2, 2⟩ (2) = some (⟨189, 0, 0⟩, ⟨140, 0, 0⟩) := by native_decide
theorem bueno52 (n j : Nat) (h : M52 n j) : Bueno n j := by
  unfold M52 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C52 [] 0 _ _ _ _ _ _ cert52 0 0
  have hn : C52.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C52, Aff.ev, ]; omega
  have hm : C52.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C52, Aff.ev, ]; omega
  have hP : (Aff.ev ⟨140, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨189, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C53 : Cono := ⟨⟨10, 5, 0⟩, ⟨4, 2, 0⟩⟩
def pre53 : List SegC := [SegC.M, SegC.P 4, SegC.A (9) (5) (0), SegC.M, SegC.P 20, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (5) (3) (0), SegC.M, SegC.P 16, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (1) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (5) (3) (0), SegC.M, SegC.P 16, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (2) (2) (0), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (2) (0)]
def per53 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (5) (3) (0), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.M, SegC.P 20, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 12, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (1) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (5) (3) (0), SegC.M, SegC.P 16, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (2) (2) (0)]
theorem cert53 : verificaS C53 [] 0 (expand pre53) (expand per53) ⟨-2, 2⟩ (2) = some (⟨385, 192, 0⟩, ⟨284, 144, 0⟩) := by native_decide
theorem bueno53 (n j : Nat) (h : M53 n j) : Bueno n j := by
  unfold M53 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C53 [] 0 _ _ _ _ _ _ cert53 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C53.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C53, Aff.ev, hqn, ]; omega
  have hm : C53.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C53, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨284, 144, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨385, 192, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C54 : Cono := ⟨⟨8, 5, 3⟩, ⟨3, 2, 1⟩⟩
def pre54 : List SegC := [SegC.M, SegC.P 4, SegC.A (7) (5) (3), SegC.M, SegC.P 20, SegC.A (2) (2) (1), SegC.P 1, SegC.M, SegC.P 4, SegC.A (4) (3) (2), SegC.M, SegC.P 16, SegC.A (2) (2) (1), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (1) (1), SegC.P 5, SegC.M, SegC.P 4, SegC.A (4) (3) (2), SegC.M, SegC.P 16, SegC.A (2) (2) (1), SegC.P 1, SegC.M, SegC.P 12, SegC.A (1) (2) (1), SegC.P 13, SegC.M, SegC.P 8, SegC.A (1) (2) (1)]
def per54 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (3) (2), SegC.M, SegC.P 16, SegC.A (1) (1) (1), SegC.M, SegC.P 20, SegC.A (0) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (0) (1), SegC.M, SegC.P 12, SegC.A (0) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (1) (1), SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (3) (2), SegC.M, SegC.P 16, SegC.A (2) (2) (1), SegC.P 1, SegC.M, SegC.P 8, SegC.A (2) (2) (1), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (2) (1)]
theorem cert54 : verificaS C54 [] 0 (expand pre54) (expand per54) ⟨-2, 2⟩ (2) = some (⟨297, 192, 104⟩, ⟨220, 144, 80⟩) := by native_decide
theorem bueno54 (n j : Nat) (h : M54 n j) : Bueno n j := by
  unfold M54 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have key := verificaS_ok C54 [] 0 _ _ _ _ _ _ cert54 q1.toNat q2.toNat
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have hn : C54.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C54, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C54.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C54, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨220, 144, 80⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨297, 192, 104⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C57 : Cono := ⟨⟨7, 0, 6⟩, ⟨3, 0, 3⟩⟩
def pre57 : List SegC := [SegC.M, SegC.P 4, SegC.A (6) (0) (6), SegC.M, SegC.P 20, SegC.A (2) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (0) (3), SegC.M, SegC.P 16, SegC.A (2) (0) (3), SegC.P 10, SegC.M, SegC.P 4, SegC.A (3) (0) (3), SegC.M, SegC.P 16, SegC.A (2) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (1) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (1) (0) (3)]
def per57 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (0) (0) (3), SegC.P 33, SegC.M, SegC.P 4, SegC.A (3) (0) (3), SegC.M, SegC.P 16, SegC.A (2) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (2) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (1) (0) (3)]
theorem cert57 : verificaS C57 [] 0 (expand pre57) (expand per57) ⟨-2, 2⟩ (2) = some (⟨281, 0, 264⟩, ⟨204, 0, 192⟩) := by native_decide
theorem bueno57 (n j : Nat) (h : M57 n j) : Bueno n j := by
  unfold M57 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C57 [] 0 _ _ _ _ _ _ cert57 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C57.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C57, Aff.ev, hqn, ]; omega
  have hm : C57.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C57, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨204, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨281, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C58 : Cono := ⟨⟨9, 0, 6⟩, ⟨4, 0, 3⟩⟩
def pre58 : List SegC := [SegC.M, SegC.P 4, SegC.A (8) (0) (6), SegC.M, SegC.P 20, SegC.A (3) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (4) (0) (3), SegC.M, SegC.P 16, SegC.A (3) (0) (3), SegC.P 10, SegC.M, SegC.P 4, SegC.A (4) (0) (3), SegC.M, SegC.P 16, SegC.A (3) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (2) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (2) (0) (3)]
def per58 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (1) (0) (3), SegC.P 33, SegC.M, SegC.P 4, SegC.A (4) (0) (3), SegC.M, SegC.P 16, SegC.A (3) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (3) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (2) (0) (3)]
theorem cert58 : verificaS C58 [] 0 (expand pre58) (expand per58) ⟨-2, 2⟩ (2) = some (⟨369, 0, 264⟩, ⟨268, 0, 192⟩) := by native_decide
theorem bueno58 (n j : Nat) (h : M58 n j) : Bueno n j := by
  unfold M58 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C58 [] 0 _ _ _ _ _ _ cert58 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C58.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C58, Aff.ev, hqn, ]; omega
  have hm : C58.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C58, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨268, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨369, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C59 : Cono := ⟨⟨11, 0, 6⟩, ⟨5, 0, 3⟩⟩
def pre59 : List SegC := [SegC.M, SegC.P 4, SegC.A (10) (0) (6), SegC.M, SegC.P 20, SegC.A (4) (0) (3), SegC.P 1, SegC.M, SegC.P 4, SegC.A (5) (0) (3), SegC.M, SegC.P 16, SegC.A (4) (0) (3), SegC.P 10, SegC.M, SegC.P 4, SegC.A (5) (0) (3), SegC.M, SegC.P 16, SegC.A (4) (0) (3), SegC.P 1, SegC.M, SegC.P 12, SegC.A (3) (0) (3), SegC.P 13, SegC.M, SegC.P 8, SegC.A (3) (0) (3)]
def per59 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (5) (0) (3), SegC.P 21, SegC.M, SegC.P 24, SegC.A (2) (0) (3), SegC.P 33, SegC.M, SegC.P 4, SegC.A (5) (0) (3), SegC.M, SegC.P 16, SegC.A (4) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (4) (0) (3), SegC.P 1, SegC.M, SegC.P 8, SegC.A (3) (0) (3)]
theorem cert59 : verificaS C59 [] 0 (expand pre59) (expand per59) ⟨-2, 2⟩ (2) = some (⟨457, 0, 264⟩, ⟨332, 0, 192⟩) := by native_decide
theorem bueno59 (n j : Nat) (h : M59 n j) : Bueno n j := by
  unfold M59 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C59 [] 0 _ _ _ _ _ _ cert59 0 q.toNat
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C59.n 0 q.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C59, Aff.ev, hqn, ]; omega
  have hm : C59.m 0 q.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C59, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨332, 0, 192⟩ 0 q.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨457, 0, 264⟩ 0 q.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C60 : Cono := ⟨⟨12, 5, 2⟩, ⟨5, 2, 1⟩⟩
def pre60 : List SegC := [SegC.M, SegC.P 4, SegC.A (11) (5) (2), SegC.M, SegC.P 20, SegC.A (4) (2) (1), SegC.P 1, SegC.M, SegC.P 4, SegC.A (6) (3) (1), SegC.M, SegC.P 16, SegC.A (4) (2) (1), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (1) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (6) (3) (1), SegC.M, SegC.P 16, SegC.A (4) (2) (1), SegC.P 1, SegC.M, SegC.P 12, SegC.A (3) (2) (1), SegC.P 13, SegC.M, SegC.P 8, SegC.A (3) (2) (1)]
def per60 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (6) (3) (1), SegC.M, SegC.P 16, SegC.A (1) (1) (0), SegC.M, SegC.P 20, SegC.A (1) (1) (0), SegC.M, SegC.P 24, SegC.A (0) (0) (1), SegC.P 1, SegC.M, SegC.P 12, SegC.A (1) (1) (0), SegC.P 1, SegC.M, SegC.P 8, SegC.A (0) (1) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (6) (3) (1), SegC.M, SegC.P 16, SegC.A (4) (2) (1), SegC.P 1, SegC.M, SegC.P 8, SegC.A (4) (2) (1), SegC.P 1, SegC.M, SegC.P 8, SegC.A (3) (2) (1)]
theorem cert60 : verificaS C60 [] 0 (expand pre60) (expand per60) ⟨-2, 2⟩ (2) = some (⟨473, 192, 88⟩, ⟨348, 144, 64⟩) := by native_decide
theorem bueno60 (n j : Nat) (h : M60 n j) : Bueno n j := by
  unfold M60 at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h
  have hq10 : 0 ≤ q1 := by omega
  have hq20 : 0 ≤ q2 := by omega
  have key := verificaS_ok C60 [] 0 _ _ _ _ _ _ cert60 q1.toNat q2.toNat
  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10
  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20
  have hn : C60.n q1.toNat q2.toNat = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C60, Aff.ev, hq1n, hq2n, ]; omega
  have hm : C60.m q1.toNat q2.toNat = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C60, Aff.ev, hq1n, hq2n, ]; omega
  have hP : (Aff.ev ⟨348, 144, 64⟩ q1.toNat q2.toNat).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  have hT : (Aff.ev ⟨473, 192, 88⟩ q1.toNat q2.toNat).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hq1n, hq2n, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C64 : Cono := ⟨⟨3, 0, 0⟩, ⟨1, 0, 0⟩⟩
def pre64 : List SegC := [SegC.M, SegC.P 4, SegC.A (2) (0) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 26, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 24]
def per64 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 20]
theorem cert64 : verificaS C64 [] 0 (expand pre64) (expand per64) ⟨-1, 1⟩ (1) = some (⟨99, 0, 0⟩, ⟨38, 0, 0⟩) := by native_decide
theorem bueno64 (n j : Nat) (h : M64 n j) : Bueno n j := by
  unfold M64 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C64 [] 0 _ _ _ _ _ _ cert64 0 0
  have hn : C64.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C64, Aff.ev, ]; omega
  have hm : C64.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C64, Aff.ev, ]; omega
  have hP : 2 * (Aff.ev ⟨38, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨99, 0, 0⟩ 0 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key⟩

def C65 : Cono := ⟨⟨9, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre65 : List SegC := [SegC.M, SegC.P 4, SegC.A (8) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (7) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (7) (6) (0), SegC.P 24]
def per65 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (7) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (7) (6) (0), SegC.P 20]
theorem cert65 : verificaS C65 [] 0 (expand pre65) (expand per65) ⟨-2, 2⟩ (2) = some (⟨195, 96, 0⟩, ⟨172, 96, 0⟩) := by native_decide
theorem bueno65 (n j : Nat) (h : M65 n j) : Bueno n j := by
  unfold M65 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C65 [] 0 _ _ _ _ _ _ cert65 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C65.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C65, Aff.ev, hqn, ]; omega
  have hm : C65.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C65, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨172, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨195, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C66 : Cono := ⟨⟨5, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre66 : List SegC := [SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 24]
def per66 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (1) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (1) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 20]
theorem cert66 : verificaS C66 [] 0 (expand pre66) (expand per66) ⟨-2, 2⟩ (2) = some (⟨131, 96, 0⟩, ⟨108, 96, 0⟩) := by native_decide
theorem bueno66 (n j : Nat) (h : M66 n j) : Bueno n j := by
  unfold M66 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C66 [] 0 _ _ _ _ _ _ cert66 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C66.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C66, Aff.ev, hqn, ]; omega
  have hm : C66.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C66, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨108, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨131, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C67 : Cono := ⟨⟨7, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre67 : List SegC := [SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 24]
def per67 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 20]
theorem cert67 : verificaS C67 [] 0 (expand pre67) (expand per67) ⟨-2, 2⟩ (2) = some (⟨163, 96, 0⟩, ⟨140, 96, 0⟩) := by native_decide
theorem bueno67 (n j : Nat) (h : M67 n j) : Bueno n j := by
  unfold M67 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C67 [] 0 _ _ _ _ _ _ cert67 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C67.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C67, Aff.ev, hqn, ]; omega
  have hm : C67.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C67, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨140, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨163, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C69 : Cono := ⟨⟨4, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre69 : List SegC := [SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (1) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 24]
def per69 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (0) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (0) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 20]
theorem cert69 : verificaS C69 [] 0 (expand pre69) (expand per69) ⟨-2, 2⟩ (2) = some (⟨115, 96, 0⟩, ⟨92, 96, 0⟩) := by native_decide
theorem bueno69 (n j : Nat) (h : M69 n j) : Bueno n j := by
  unfold M69 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C69 [] 0 _ _ _ _ _ _ cert69 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C69.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C69, Aff.ev, hqn, ]; omega
  have hm : C69.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C69, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨92, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨115, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C70 : Cono := ⟨⟨6, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre70 : List SegC := [SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (3) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 24]
def per70 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (2) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 20]
theorem cert70 : verificaS C70 [] 0 (expand pre70) (expand per70) ⟨-2, 2⟩ (2) = some (⟨147, 96, 0⟩, ⟨124, 96, 0⟩) := by native_decide
theorem bueno70 (n j : Nat) (h : M70 n j) : Bueno n j := by
  unfold M70 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C70 [] 0 _ _ _ _ _ _ cert70 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C70.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C70, Aff.ev, hqn, ]; omega
  have hm : C70.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C70, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨124, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨147, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C71 : Cono := ⟨⟨8, 6, 0⟩, ⟨1, 0, 0⟩⟩
def pre71 : List SegC := [SegC.M, SegC.P 4, SegC.A (7) (6) (0), SegC.P 21, SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (5) (6) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 24]
def per71 : List SegC := [SegC.P 10, SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 17, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 9, SegC.M, SegC.P 4, SegC.A (4) (6) (0), SegC.P 4, SegC.M, SegC.P 4, SegC.A (6) (6) (0), SegC.P 20]
theorem cert71 : verificaS C71 [] 0 (expand pre71) (expand per71) ⟨-2, 2⟩ (2) = some (⟨179, 96, 0⟩, ⟨156, 96, 0⟩) := by native_decide
theorem bueno71 (n j : Nat) (h : M71 n j) : Bueno n j := by
  unfold M71 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C71 [] 0 _ _ _ _ _ _ cert71 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C71.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C71, Aff.ev, hqn, ]; omega
  have hm : C71.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C71, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨156, 96, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 20 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨179, 96, 0⟩ q.toNat 0).toNat ≤ 204 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C74 : Cono := ⟨⟨2, 0, 0⟩, ⟨0, 0, 0⟩⟩
def pre74 : List SegC := [SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 8]
def per74 : List SegC := [SegC.P 2, SegC.M, SegC.P 4, SegC.A (1) (0) (0), SegC.P 8]
theorem cert74 : verificaS C74 [] 0 (expand pre74) (expand per74) ⟨1, -1⟩ (3) = some (⟨75, 0, 0⟩, ⟨18, 0, 0⟩) := by native_decide
theorem bueno74 (n j : Nat) (h : M74 n j) : BuenoUno n j := by
  unfold M74 at h
  obtain ⟨hn0, hj0⟩ := h
  have key := verificaS_ok C74 [] 0 _ _ _ _ _ _ cert74 0 0
  have hn : C74.n 0 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C74, Aff.ev, ]; omega
  have hm : C74.m 0 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C74, Aff.ev, ]; omega
  have hP : 2 * (Aff.ev ⟨18, 0, 0⟩ 0 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, ]; omega
  have hT : (Aff.ev ⟨75, 0, 0⟩ 0 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key⟩

def C75 : Cono := ⟨⟨4, 2, 0⟩, ⟨0, 0, 0⟩⟩
def pre75 : List SegC := [SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (2) (0)]
def per75 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (3) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (2) (0)]
theorem cert75 : verificaS C75 [] 0 (expand pre75) (expand per75) ⟨2, -2⟩ (6) = some (⟨171, 80, 0⟩, ⟨68, 32, 0⟩) := by native_decide
theorem bueno75 (n j : Nat) (h : M75 n j) : BuenoUno n j := by
  unfold M75 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C75 [] 0 _ _ _ _ _ _ cert75 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C75.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C75, Aff.ev, hqn, ]; omega
  have hm : C75.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C75, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨68, 32, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨171, 80, 0⟩ q.toNat 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

def C76 : Cono := ⟨⟨3, 2, 0⟩, ⟨0, 0, 0⟩⟩
def pre76 : List SegC := [SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 6, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (2) (0), SegC.P 5, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (0) (2) (0)]
def per76 : List SegC := [SegC.P 4, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 10, SegC.M, SegC.P 4, SegC.A (2) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (1) (2) (0), SegC.P 1, SegC.M, SegC.P 4, SegC.A (0) (2) (0)]
theorem cert76 : verificaS C76 [] 0 (expand pre76) (expand per76) ⟨2, -2⟩ (6) = some (⟨131, 80, 0⟩, ⟨52, 32, 0⟩) := by native_decide
theorem bueno76 (n j : Nat) (h : M76 n j) : BuenoUno n j := by
  unfold M76 at h
  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h
  have hq0 : 0 ≤ q := by omega
  have key := verificaS_ok C76 [] 0 _ _ _ _ _ _ cert76 q.toNat 0
  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0
  have hn : C76.n q.toNat 0 = n := by
    simp only [Cono.n]; apply toNat_eq; simp only [C76, Aff.ev, hqn, ]; omega
  have hm : C76.m q.toNat 0 = 2 * j + 1 := by
    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C76, Aff.ev, hqn, ]; omega
  have hP : (Aff.ev ⟨52, 32, 0⟩ q.toNat 0).toNat = 16 * (n + 2 * j + 1) - 12 := by
    simp only [Aff.ev, hqn, ]; omega
  have hT : (Aff.ev ⟨131, 80, 0⟩ q.toNat 0).toNat ≤ 40 * (n + 2 * j + 1) := by
    simp only [Aff.ev, hqn, ]; omega
  simp only [Cono.R, hn, hm, concA_nil] at key
  exact ⟨_, hT, _, by rw [← hP]; exact key⟩

theorem cubre73 (n j : Nat) (h : M73 n j) : M74 n j ∨ M75 n j := by
  unfold M73 at h; unfold M74; unfold M75; omega
theorem bueno73 (n j : Nat) (h : M73 n j)  : BuenoUno n j := by
  rcases cubre73 n j h with h | h
  · exact bueno74 n j h
  · exact bueno75 n j h

theorem cubre72 (n j : Nat) (h : M72 n j) : M73 n j ∨ M76 n j := by
  unfold M72 at h; unfold M73; unfold M76; omega
theorem bueno72 (n j : Nat) (h : M72 n j)  : BuenoUno n j := by
  rcases cubre72 n j h with h | h
  · exact bueno73 n j h
  · exact bueno76 n j h

theorem cubre68 (n j : Nat) (h : M68 n j) : M69 n j ∨ M70 n j ∨ M71 n j := by
  unfold M68 at h; unfold M69; unfold M70; unfold M71; omega
theorem bueno68 (n j : Nat) (h : M68 n j)  : Bueno n j := by
  rcases cubre68 n j h with h | h | h
  · exact bueno69 n j h
  · exact bueno70 n j h
  · exact bueno71 n j h

theorem cubre63 (n j : Nat) (h : M63 n j) : M64 n j ∨ M65 n j := by
  unfold M63 at h; unfold M64; unfold M65; omega
theorem bueno63 (n j : Nat) (h : M63 n j)  : Bueno n j := by
  rcases cubre63 n j h with h | h
  · exact bueno64 n j h
  · exact bueno65 n j h

theorem cubre62 (n j : Nat) (h : M62 n j) : M63 n j ∨ M66 n j ∨ M67 n j := by
  unfold M62 at h; unfold M63; unfold M66; unfold M67; omega
theorem bueno62 (n j : Nat) (h : M62 n j)  : Bueno n j := by
  rcases cubre62 n j h with h | h | h
  · exact bueno63 n j h
  · exact bueno66 n j h
  · exact bueno67 n j h

theorem cubre61 (n j : Nat) (h : M61 n j) : M62 n j ∨ M68 n j := by
  unfold M61 at h; unfold M62; unfold M68; omega
theorem bueno61 (n j : Nat) (h : M61 n j)  : Bueno n j := by
  rcases cubre61 n j h with h | h
  · exact bueno62 n j h
  · exact bueno68 n j h

theorem cubre56 (n j : Nat) (h : M56 n j) : M57 n j ∨ M58 n j ∨ M59 n j := by
  unfold M56 at h; unfold M57; unfold M58; unfold M59; omega
theorem bueno56 (n j : Nat) (h : M56 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre56 n j h with h | h | h
  · exact bueno57 n j h
  · exact bueno58 n j h
  · exact bueno59 n j h

theorem cubre55 (n j : Nat) (h : M55 n j) : M56 n j ∨ M60 n j := by
  unfold M55 at h; unfold M56; unfold M60; omega
theorem bueno55 (n j : Nat) (h : M55 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre55 n j h with h | h
  · exact bueno56 n j h hex
  · exact bueno60 n j h

theorem cubre51 (n j : Nat) (h : M51 n j) : M52 n j ∨ M53 n j := by
  unfold M51 at h; unfold M52; unfold M53; omega
theorem bueno51 (n j : Nat) (h : M51 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre51 n j h with h | h
  · exact bueno52 n j h
  · exact bueno53 n j h

theorem cubre50 (n j : Nat) (h : M50 n j) : M51 n j ∨ M54 n j := by
  unfold M50 at h; unfold M51; unfold M54; omega
theorem bueno50 (n j : Nat) (h : M50 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre50 n j h with h | h
  · exact bueno51 n j h hex
  · exact bueno54 n j h

theorem cubre49 (n j : Nat) (h : M49 n j) : M50 n j ∨ M55 n j := by
  unfold M49 at h; unfold M50; unfold M55; omega
theorem bueno49 (n j : Nat) (h : M49 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre49 n j h with h | h
  · exact bueno50 n j h hex
  · exact bueno55 n j h hex

theorem cubre46 (n j : Nat) (h : M46 n j) : M47 n j ∨ M48 n j := by
  unfold M46 at h; unfold M47; unfold M48; omega
theorem bueno46 (n j : Nat) (h : M46 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre46 n j h with h | h
  · exact bueno47 n j h
  · exact bueno48 n j h

theorem cubre45 (n j : Nat) (h : M45 n j) : M46 n j ∨ M49 n j := by
  unfold M45 at h; unfold M46; unfold M49; omega
theorem bueno45 (n j : Nat) (h : M45 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre45 n j h with h | h
  · exact bueno46 n j h hex
  · exact bueno49 n j h hex

theorem cubre42 (n j : Nat) (h : M42 n j) : M43 n j ∨ M44 n j := by
  unfold M42 at h; unfold M43; unfold M44; omega
theorem bueno42 (n j : Nat) (h : M42 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre42 n j h with h | h
  · exact bueno43 n j h
  · exact bueno44 n j h

theorem cubre40 (n j : Nat) (h : M40 n j) : M41 n j ∨ M42 n j := by
  unfold M40 at h; unfold M41; unfold M42; omega
theorem bueno40 (n j : Nat) (h : M40 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre40 n j h with h | h
  · exact bueno41 n j h
  · exact bueno42 n j h hex

theorem cubre38 (n j : Nat) (h : M38 n j) : M39 n j ∨ M40 n j := by
  unfold M38 at h; unfold M39; unfold M40; omega
theorem bueno38 (n j : Nat) (h : M38 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre38 n j h with h | h
  · exact bueno39 n j h
  · exact bueno40 n j h hex

theorem cubre35 (n j : Nat) (h : M35 n j) : M36 n j ∨ M37 n j := by
  unfold M35 at h; unfold M36; unfold M37; omega
theorem bueno35 (n j : Nat) (h : M35 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre35 n j h with h | h
  · exact bueno36 n j h
  · exact bueno37 n j h

theorem cubre33 (n j : Nat) (h : M33 n j) : M34 n j ∨ M35 n j := by
  unfold M33 at h; unfold M34; unfold M35; omega
theorem bueno33 (n j : Nat) (h : M33 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre33 n j h with h | h
  · exact bueno34 n j h
  · exact bueno35 n j h hex

theorem cubre31 (n j : Nat) (h : M31 n j) : M32 n j ∨ M33 n j := by
  unfold M31 at h; unfold M32; unfold M33; omega
theorem bueno31 (n j : Nat) (h : M31 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre31 n j h with h | h
  · exact bueno32 n j h
  · exact bueno33 n j h hex

theorem cubre28 (n j : Nat) (h : M28 n j) : M29 n j ∨ M30 n j := by
  unfold M28 at h; unfold M29; unfold M30; omega
theorem bueno28 (n j : Nat) (h : M28 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre28 n j h with h | h
  · exact bueno29 n j h
  · exact bueno30 n j h

theorem cubre26 (n j : Nat) (h : M26 n j) : M27 n j ∨ M28 n j := by
  unfold M26 at h; unfold M27; unfold M28; omega
theorem bueno26 (n j : Nat) (h : M26 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre26 n j h with h | h
  · exact bueno27 n j h
  · exact bueno28 n j h hex

theorem cubre24 (n j : Nat) (h : M24 n j) : M25 n j ∨ M26 n j := by
  unfold M24 at h; unfold M25; unfold M26; omega
theorem bueno24 (n j : Nat) (h : M24 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre24 n j h with h | h
  · exact bueno25 n j h
  · exact bueno26 n j h hex

theorem cubre23 (n j : Nat) (h : M23 n j) : M24 n j ∨ M31 n j ∨ M38 n j := by
  unfold M23 at h; unfold M24; unfold M31; unfold M38; omega
theorem bueno23 (n j : Nat) (h : M23 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre23 n j h with h | h | h
  · exact bueno24 n j h hex
  · exact bueno31 n j h hex
  · exact bueno38 n j h hex

theorem cubre21 (n j : Nat) (h : M21 n j) : M22 n j ∨ M23 n j := by
  unfold M21 at h; unfold M22; unfold M23; omega
theorem bueno21 (n j : Nat) (h : M21 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre21 n j h with h | h
  · exact bueno22 n j h
  · exact bueno23 n j h hex

theorem cubre19 (n j : Nat) (h : M19 n j) : M20 n j ∨ M21 n j := by
  unfold M19 at h; unfold M20; unfold M21; omega
theorem bueno19 (n j : Nat) (h : M19 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre19 n j h with h | h
  · exact bueno20 n j h
  · exact bueno21 n j h hex

theorem cubre17 (n j : Nat) (h : M17 n j) : M18 n j ∨ M19 n j := by
  unfold M17 at h; unfold M18; unfold M19; omega
theorem bueno17 (n j : Nat) (h : M17 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre17 n j h with h | h
  · exact bueno18 n j h
  · exact bueno19 n j h hex

theorem cubre15 (n j : Nat) (h : M15 n j) : M16 n j ∨ M17 n j := by
  unfold M15 at h; unfold M16; unfold M17; omega
theorem bueno15 (n j : Nat) (h : M15 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre15 n j h with h | h
  · exact bueno16 n j h
  · exact bueno17 n j h hex

theorem cubre13 (n j : Nat) (h : M13 n j) : M14 n j ∨ M15 n j := by
  unfold M13 at h; unfold M14; unfold M15; omega
theorem bueno13 (n j : Nat) (h : M13 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre13 n j h with h | h
  · exact bueno14 n j h
  · exact bueno15 n j h hex

theorem bueno10 (n j : Nat) (h : M10 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  unfold M10 at h; exact absurd (by omega) hex

theorem cubre9 (n j : Nat) (h : M9 n j) : M10 n j ∨ M11 n j ∨ M12 n j ∨ M13 n j := by
  unfold M9 at h; unfold M10; unfold M11; unfold M12; unfold M13; omega
theorem bueno9 (n j : Nat) (h : M9 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre9 n j h with h | h | h | h
  · exact bueno10 n j h hex
  · exact bueno11 n j h
  · exact bueno12 n j h
  · exact bueno13 n j h hex

theorem cubre7 (n j : Nat) (h : M7 n j) : M8 n j ∨ M9 n j := by
  unfold M7 at h; unfold M8; unfold M9; omega
theorem bueno7 (n j : Nat) (h : M7 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre7 n j h with h | h
  · exact bueno8 n j h
  · exact bueno9 n j h hex

theorem cubre5 (n j : Nat) (h : M5 n j) : M6 n j ∨ M7 n j := by
  unfold M5 at h; unfold M6; unfold M7; omega
theorem bueno5 (n j : Nat) (h : M5 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre5 n j h with h | h
  · exact bueno6 n j h
  · exact bueno7 n j h hex

theorem cubre3 (n j : Nat) (h : M3 n j) : M4 n j ∨ M5 n j := by
  unfold M3 at h; unfold M4; unfold M5; omega
theorem bueno3 (n j : Nat) (h : M3 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre3 n j h with h | h
  · exact bueno4 n j h
  · exact bueno5 n j h hex

theorem cubre1 (n j : Nat) (h : M1 n j) : M2 n j ∨ M3 n j := by
  unfold M1 at h; unfold M2; unfold M3; omega
theorem bueno1 (n j : Nat) (h : M1 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre1 n j h with h | h
  · exact bueno2 n j h
  · exact bueno3 n j h hex

theorem cubre0 (n j : Nat) (h : M0 n j) : M1 n j ∨ M45 n j := by
  unfold M0 at h; unfold M1; unfold M45; omega
theorem bueno0 (n j : Nat) (h : M0 n j) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j := by
  rcases cubre0 n j h with h | h
  · exact bueno1 n j h hex
  · exact bueno45 n j h hex

/-- **Teorema.** Para m = 2j+1 con j ≥ 2 (m ≥ 5) y n ≥ m - 1, salvo (n, m) = (12, 13), la hormiga RⁿLᵐ
desde el tablero en blanco entra, a más tardar en el paso 204·(n + m), en una autopista con periodo 16(n + m) - 20. -/
theorem ley_m5 (n j : Nat) (hj : 2 ≤ j) (hn : 2 * j ≤ n) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j :=
  bueno0 n j (by unfold M0; omega) hex

/-- **Teorema (m = 3).** Para n ≥ 3, la hormiga RⁿLLL desde el blanco entra, a más tardar en el paso 204·(n + 3),
en una autopista con periodo 16(n + 3) - 20. -/
theorem ley_m3 (n : Nat) (hn : 3 ≤ n) : Bueno n 1 :=
  bueno61 n 1 (by unfold M61; omega)

/-- **Teorema (m = 1, familia RⁿL; LⁿR en espejo).** Para n ≥ 2, la hormiga RⁿL desde el blanco entra, a más
tardar en el paso 40·(n + 1), en una autopista con periodo 16n + 4 (para n = 2 se repite ya a la mitad: 18). -/
theorem ley_m1 (n : Nat) (hn : 2 ≤ n) : BuenoUno n 0 :=
  bueno72 n 0 (by unfold M72; omega)

theorem ley_RnL (n : Nat) (hn : 2 ≤ n) :
    ∃ t1 : Nat, t1 ≤ 40 * (n + 1) ∧ ∃ d : Pt, EsAutopista (RL n 1) (iter (RL n 1) t1 blanco.toE) (16 * n + 4) d := by
  obtain ⟨t1, h1, d, h2⟩ := ley_m1 n hn
  refine ⟨t1, by omega, d, ?_⟩
  have e1 : 2 * 0 + 1 = 1 := rfl
  have e2 : 16 * (n + 2 * 0 + 1) - 12 = 16 * n + 4 := by omega
  rw [e1, e2] at h2; exact h2

end Hormiga
