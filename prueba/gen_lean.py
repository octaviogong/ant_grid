"""Genera Hormiga/Certificados.lean a partir de arbol_B.json.

Para cada nodo del árbol de casos se define su región M_k(n, j) con condiciones lineales y de
divisibilidad (sin existenciales), para que `omega` pueda probar que los hijos cubren al padre.
Cada hoja se cierra con `verificaS_ok` aplicado a su certificado (evaluado con `native_decide`).
"""
import json, sys
TACTICA = sys.argv[1] if len(sys.argv) > 1 else 'native_decide'
from simbolico import fmtc

data = json.load(open("arbol_B.json"))

def segc(txt):
    out = []
    for tok in txt.split():
        if tok[0] == "P": out.append(f"SegC.P {int(tok[1:])}")
        elif tok == "M": out.append("SegC.M")
        else:
            a, b, c = (int(x) for x in tok[1:].split(","))
            out.append(f"SegC.A ({a}) ({b}) ({c})")
    return "[" + ", ".join(out) + "]"

def lean_aff(f): return f"⟨{f[0]}, {f[1]}, {f[2]}⟩"

def cond(nf, jf):
    """Condición (Lean, sobre n j : Nat) de que existan s, t ≥ 0 con n = nf(s,t), j = jf(s,t)."""
    a, b, c = nf; d, e, f = jf
    N, J = "(n:Int)", "(j:Int)"
    us, ut = (b != 0 or e != 0), (c != 0 or f != 0)
    def lin(k0, kn, kj):  # k0 + kn*N + kj*J
        return f"({k0} + {kn}*{N} + {kj}*{J})"
    if not us and not ut:
        return f"({N} = {a} ∧ {J} = {d})", None
    if us and not ut:
        # n - a = b s, j - d = e s
        if b != 0:
            num = lin(-a, 1, 0); den = b
            other = f"({e}*{lin(-a,1,0)} = {b}*{lin(-d,0,1)})"
        else:
            num = lin(-d, 0, 1); den = e
            other = f"({N} = {a})"
        sgn = "0 ≤" if den > 0 else "0 ≥"
        return f"(({abs(den)}:Int) ∣ {num} ∧ {sgn} {num} ∧ {other})", ("s", num, den)
    if ut and not us:
        if c != 0:
            num = lin(-a, 1, 0); den = c
            other = f"({f}*{lin(-a,1,0)} = {c}*{lin(-d,0,1)})"
        else:
            num = lin(-d, 0, 1); den = f
            other = f"({N} = {a})"
        sgn = "0 ≤" if den > 0 else "0 ≥"
        return f"(({abs(den)}:Int) ∣ {num} ∧ {sgn} {num} ∧ {other})", ("t", num, den)
    det = b * f - c * e
    assert det != 0, (nf, jf)
    # s = (f(n-a) - c(j-d))/det ; t = (b(j-d) - e(n-a))/det
    g = 1 if det > 0 else -1
    ns = lin(g * (-f * a + c * d), g * f, -g * c); nt = lin(g * (-b * d + e * a), -g * e, g * b)
    return (f"(({abs(det)}:Int) ∣ {ns} ∧ ({abs(det)}:Int) ∣ {nt} ∧ 0 ≤ {ns} ∧ 0 ≤ {nt})", ("st", ns, nt, abs(det)))

lines = []
P = lines.append
P("""/-
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
""")

counter = [0]
nodes = []   # (id, cond, kind, payload)

def walk(t, tag):
    i = counter[0]; counter[0] += 1
    c, inv = cond(t["n"], t["j"])
    node = dict(id=i, cond=c, inv=inv, tipo=t["tipo"], tag=tag, n=t["n"], j=t["j"])
    nodes.append(node)
    if t["tipo"] == "nodo":
        node["hijos"] = [walk(h, tag) for h in t["hijos"]]
    elif t["tipo"] == "hoja":
        node["cert"] = t["cert"]
    return i

roots = {name: walk(t, name) for name, t in data.items()}

for nd in nodes:
    P(f"def M{nd['id']} (n j : Nat) : Prop := {nd['cond']}")
P("")

PRED = {"m5": "Bueno", "m3": "Bueno", "m1": "BuenoUno"}
CTE = {"m5": 20, "m3": 20, "m1": 12}
COTA = {"m5": 204, "m3": 204, "m1": 40}
def law_aff(nf, jf, cte=20):
    return [16 * (nf[0] + 2 * jf[0] + 1) - cte, 16 * (nf[1] + 2 * jf[1]), 16 * (nf[2] + 2 * jf[2])]

# hojas
for nd in nodes:
    if nd["tipo"] != "hoja": continue
    c = nd["cert"]; i = nd["id"]
    nf, jf = nd["n"], nd["j"]
    T1, Pp = c["inicio"], c["P"]
    d = c["deriva"]
    tag = nd["tag"]; pred = PRED[tag]; cte = CTE[tag]; cota = COTA[tag]
    law = law_aff(nf, jf, cte)
    mitad = [2 * x for x in Pp] == law
    assert Pp == law or mitad, (nf, jf, Pp, law)
    P(f"def C{i} : Cono := ⟨{lean_aff(nf)}, {lean_aff(jf)}⟩")
    P(f"def pre{i} : List SegC := {segc(c['pre'])}")
    P(f"def per{i} : List SegC := {segc(c['per'])}")
    P(f"theorem cert{i} : verificaS C{i} [] 0 (expand pre{i}) (expand per{i}) ⟨{d[0]}, {d[1]}⟩ ({c['f0']}) = some ({lean_aff(T1)}, {lean_aff(Pp)}) := by {TACTICA}")
    # hoja → Bueno
    kind, *rest = nd["inv"] if nd["inv"] else ("pt",)
    P(f"theorem bueno{i} (n j : Nat) (h : M{i} n j) : {pred} n j := by")
    P(f"  unfold M{i} at h")
    if kind == "pt":
        P(f"  obtain ⟨hn0, hj0⟩ := h")
        P(f"  have key := verificaS_ok C{i} [] 0 _ _ _ _ _ _ cert{i} 0 0")
        sv, tv = "0", "0"
    elif kind == "s":
        num, den = rest
        P(f"  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h")
        P(f"  have hq0 : 0 ≤ q := by omega")
        P(f"  have key := verificaS_ok C{i} [] 0 _ _ _ _ _ _ cert{i} q.toNat 0")
        P(f"  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0")
        sv, tv = "q.toNat", "0"
    elif kind == "t":
        num, den = rest
        P(f"  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h")
        P(f"  have hq0 : 0 ≤ q := by omega")
        P(f"  have key := verificaS_ok C{i} [] 0 _ _ _ _ _ _ cert{i} 0 q.toNat")
        P(f"  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0")
        sv, tv = "0", "q.toNat"
    else:
        ns, nt, det = rest
        P(f"  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h")
        P(f"  have hq10 : 0 ≤ q1 := by omega")
        P(f"  have hq20 : 0 ≤ q2 := by omega")
        P(f"  have key := verificaS_ok C{i} [] 0 _ _ _ _ _ _ cert{i} q1.toNat q2.toNat")
        P(f"  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10")
        P(f"  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20")
        sv, tv = "q1.toNat", "q2.toNat"
    sign = "" if True else ""
    # n, m del cono coinciden con n, 2j+1
    hyps = {"pt": "", "s": "hqn, ", "t": "hqn, ", "st": "hq1n, hq2n, "}[kind]
    P(f"  have hn : C{i}.n {sv} {tv} = n := by")
    P(f"    simp only [Cono.n]; apply toNat_eq; simp only [C{i}, Aff.ev, {hyps}]; omega")
    P(f"  have hm : C{i}.m {sv} {tv} = 2 * j + 1 := by")
    P(f"    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C{i}, Aff.ev, {hyps}]; omega")
    P(f"  have hP : {'2 * ' if mitad else ''}(Aff.ev {lean_aff(Pp)} {sv} {tv}).toNat = 16 * (n + 2 * j + 1) - {cte} := by")
    P(f"    simp only [Aff.ev, {hyps}]; omega")
    P(f"  have hT : (Aff.ev {lean_aff(T1)} {sv} {tv}).toNat ≤ {cota} * (n + 2 * j + 1) := by")
    P(f"    simp only [Aff.ev, {hyps}]; omega")
    P(f"  simp only [Cono.R, hn, hm, concA_nil] at key")
    if mitad:
        P(f"  exact ⟨_, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key⟩")
    else:
        P(f"  exact ⟨_, hT, _, by rw [← hP]; exact key⟩")
    P("")

# nodos internos y fallas (de abajo hacia arriba)
for nd in reversed(nodes):
    i = nd["id"]
    if nd["tipo"] == "hoja": continue
    ex = "(hex : ¬(n = 12 ∧ j = 6))" if nd["tag"] == "m5" else ""
    if nd["tipo"] == "falla":
        P(f"theorem bueno{i} (n j : Nat) (h : M{i} n j) {ex} : {PRED[nd['tag']]} n j := by")
        P(f"  unfold M{i} at h; exact absurd (by omega) hex")
        P("")
        continue
    hs = nd["hijos"]
    disj = " ∨ ".join(f"M{c} n j" for c in hs)
    P(f"theorem cubre{i} (n j : Nat) (h : M{i} n j) : {disj} := by")
    P(f"  unfold M{i} at h; " + " ".join(f"unfold M{c};" for c in hs) + " omega")
    pat = " | ".join("h" for _ in hs)
    P(f"theorem bueno{i} (n j : Nat) (h : M{i} n j) {ex} : {PRED[nd['tag']]} n j := by")
    P(f"  rcases cubre{i} n j h with {pat}")
    for c in hs:
        cn = nodes[c]
        needs_ex = nd["tag"] == "m5" and (cn["tipo"] != "hoja")
        P(f"  · exact bueno{c} n j h" + (" hex" if needs_ex else ""))
    P("")

r5, r3, r1 = roots["m5"], roots["m3"], roots["m1"]
P(f"""/-- **Teorema.** Para m = 2j+1 con j ≥ 2 (m ≥ 5) y n ≥ m - 1, salvo (n, m) = (12, 13), la hormiga RⁿLᵐ
desde el tablero en blanco entra, a más tardar en el paso 204·(n + m), en una autopista con periodo 16(n + m) - 20. -/
theorem ley_m5 (n j : Nat) (hj : 2 ≤ j) (hn : 2 * j ≤ n) (hex : ¬(n = 12 ∧ j = 6)) : Bueno n j :=
  bueno{r5} n j (by unfold M{r5}; omega) hex

/-- **Teorema (m = 3).** Para n ≥ 3, la hormiga RⁿLLL desde el blanco entra, a más tardar en el paso 204·(n + 3),
en una autopista con periodo 16(n + 3) - 20. -/
theorem ley_m3 (n : Nat) (hn : 3 ≤ n) : Bueno n 1 :=
  bueno{r3} n 1 (by unfold M{r3}; omega)

/-- **Teorema (m = 1, familia RⁿL; LⁿR en espejo).** Para n ≥ 2, la hormiga RⁿL desde el blanco entra, a más
tardar en el paso 40·(n + 1), en una autopista con periodo 16n + 4 (para n = 2 se repite ya a la mitad: 18). -/
theorem ley_m1 (n : Nat) (hn : 2 ≤ n) : BuenoUno n 0 :=
  bueno{r1} n 0 (by unfold M{r1}; omega)

theorem ley_RnL (n : Nat) (hn : 2 ≤ n) :
    ∃ t1 : Nat, t1 ≤ 40 * (n + 1) ∧ ∃ d : Pt, EsAutopista (RL n 1) (iter (RL n 1) t1 blanco.toE) (16 * n + 4) d := by
  obtain ⟨t1, h1, d, h2⟩ := ley_m1 n hn
  refine ⟨t1, by omega, d, ?_⟩
  have e1 : 2 * 0 + 1 = 1 := rfl
  have e2 : 16 * (n + 2 * 0 + 1) - 12 = 16 * n + 4 := by omega
  rw [e1, e2] at h2; exact h2

end Hormiga
""")
open("../lean/Hormiga/Certificados.lean", "w", encoding="utf-8").write("\n".join(lines))
print("nodos:", len(nodes), "hojas:", sum(1 for n in nodes if n["tipo"] == "hoja"))
