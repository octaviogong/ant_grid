"""Genera lean/Hormiga/HerenciaCert.lean: los certificados del árbol de casos re-verificados con el
verificador U (conteos de visitas), para los (n, j) con n ≥ 2j + 1. Reutiliza M_k, C_k, pre_k, per_k y
cubre_k de Certificados.lean (mismo recorrido del árbol que prueba/gen_lean.py)."""
import json, sys, os
RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TACTICA = sys.argv[1] if len(sys.argv) > 1 else 'native_decide'
data = json.load(open(os.path.join(RAIZ, 'prueba/arbol_B.json')))

def cond_kind(nf, jf):
    a, b, c = nf; d, e, f = jf
    us, ut = (b != 0 or e != 0), (c != 0 or f != 0)
    if not us and not ut: return ("pt",)
    if us and not ut: return ("s",)
    if ut and not us: return ("t",)
    return ("st",)

counter = [0]; nodes = []
def walk(t, tag):
    i = counter[0]; counter[0] += 1
    node = dict(id=i, tipo=t["tipo"], tag=tag, n=t["n"], j=t["j"], inv=cond_kind(t["n"], t["j"]))
    nodes.append(node)
    if t["tipo"] == "nodo": node["hijos"] = [walk(h, tag) for h in t["hijos"]]
    elif t["tipo"] == "hoja": node["cert"] = t["cert"]
    return i
roots = {name: walk(t, name) for name, t in data.items()}

def lean_aff(f): return f"⟨{f[0]}, {f[1]}, {f[2]}⟩"
def linea(nd): return nd["n"][0] == 2 * nd["j"][0] and nd["n"][1] == 2 * nd["j"][1] and nd["n"][2] == 2 * nd["j"][2]

L = []; P = L.append
P("""/-
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
""")
PRED = {"m5": "BuenoH", "m3": "BuenoH", "m1": "BuenoHUno"}
CTE = {"m5": 20, "m3": 20, "m1": 12}; COTA = {"m5": 204, "m3": 204, "m1": 40}
def law_aff(nf, jf, cte):
    return [16 * (nf[0] + 2 * jf[0] + 1) - cte, 16 * (nf[1] + 2 * jf[1]), 16 * (nf[2] + 2 * jf[2])]
HL = "(hl : 2 * j + 1 ≤ n)"
nhojas = 0
for nd in nodes:
    i = nd["id"]; pred = PRED[nd["tag"]]
    if nd["tipo"] == "falla" or (nd["tipo"] == "hoja" and linea(nd)):
        P(f"theorem buenoH{i} (n j : Nat) (h : M{i} n j) {HL} : {pred} n j := by")
        P(f"  unfold M{i} at h; exact absurd hl (by omega)")
        P("")
        continue
    if nd["tipo"] != "hoja": continue
    nhojas += 1
    c = nd["cert"]; nf, jf = nd["n"], nd["j"]; T1, Pp, d = c["inicio"], c["P"], c["deriva"]
    tag = nd["tag"]; cte = CTE[tag]; cota = COTA[tag]
    law = law_aff(nf, jf, cte); mitad = [2 * x for x in Pp] == law
    assert Pp == law or mitad
    P(f"theorem certU{i} : verificaU C{i} (expand pre{i}) (expand per{i}) ⟨{d[0]}, {d[1]}⟩ ({c['f0']}) = some ({lean_aff(T1)}, {lean_aff(Pp)}) := by {TACTICA}")
    kind = nd["inv"][0]
    P(f"theorem buenoH{i} (n j : Nat) (h : M{i} n j) {HL} : {pred} n j := by")
    P(f"  unfold M{i} at h")
    if kind == "pt":
        P("  obtain ⟨hn0, hj0⟩ := h"); sv, tv = "0", "0"
    elif kind in ("s", "t"):
        P("  obtain ⟨⟨q, hq⟩, hpos, hoth⟩ := h"); P("  have hq0 : 0 ≤ q := by omega")
        P("  have hqn : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq0")
        sv, tv = ("q.toNat", "0") if kind == "s" else ("0", "q.toNat")
    else:
        P("  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, hp1, hp2⟩ := h")
        P("  have hq10 : 0 ≤ q1 := by omega"); P("  have hq20 : 0 ≤ q2 := by omega")
        P("  have hq1n : ((q1.toNat : Nat) : Int) = q1 := Int.toNat_of_nonneg hq10")
        P("  have hq2n : ((q2.toNat : Nat) : Int) = q2 := Int.toNat_of_nonneg hq20")
        sv, tv = "q1.toNat", "q2.toNat"
    hyps = {"pt": "", "s": "hqn, ", "t": "hqn, ", "st": "hq1n, hq2n, "}[kind]
    P(f"  have key := verificaU_ok C{i} _ _ _ _ _ _ certU{i} {sv} {tv}")
    P(f"  have hn : C{i}.n {sv} {tv} = n := by")
    P(f"    simp only [Cono.n]; apply toNat_eq; simp only [C{i}, Aff.ev, {hyps}]; omega")
    P(f"  have hm : C{i}.m {sv} {tv} = 2 * j + 1 := by")
    P(f"    simp only [Cono.m]; congr 1; congr 1; apply toNat_eq; simp only [C{i}, Aff.ev, {hyps}]; omega")
    P(f"  have hK : (C{i}.Kf.ev {sv} {tv}).toNat = (n + (2 * j + 1)) + n := by")
    P(f"    apply toNat_eq; simp only [Cono.Kf, Cono.Nf, Aff.ev_add, Aff.ev_mulN, Aff.ev_k]; simp only [C{i}, Aff.ev, {hyps}]; omega")
    P(f"  have hP : {'2 * ' if mitad else ''}(Aff.ev {lean_aff(Pp)} {sv} {tv}).toNat = 16 * (n + 2 * j + 1) - {cte} := by")
    P(f"    simp only [Aff.ev, {hyps}]; omega")
    P(f"  have hT : (Aff.ev {lean_aff(T1)} {sv} {tv}).toNat ≤ {cota} * (n + 2 * j + 1) := by")
    P(f"    simp only [Aff.ev, {hyps}]; omega")
    P(f"  simp only [Cono.U, hn, hm, E0U, concA_nil, hK] at key")
    if mitad:
        P(f"  exact ⟨key.2, _, hT, _, by rw [← hP]; exact autopista_doble _ _ _ _ key.1⟩")
    else:
        P(f"  exact ⟨key.2, _, hT, _, by rw [← hP]; exact key.1⟩")
    P("")
for nd in reversed(nodes):
    if nd["tipo"] != "nodo": continue
    i = nd["id"]; hs = nd["hijos"]; pat = " | ".join("h" for _ in hs)
    P(f"theorem buenoH{i} (n j : Nat) (h : M{i} n j) {HL} : {PRED[nd['tag']]} n j := by")
    P(f"  rcases cubre{i} n j h with {pat}")
    for c in hs: P(f"  · exact buenoH{c} n j h hl")
    P("")
r5, r3, r1 = roots["m5"], roots["m3"], roots["m1"]
P(f"""theorem visitas_m5 (n j : Nat) (hj : 2 ≤ j) (hn : 2 * j + 1 ≤ n) : BuenoH n j :=
  buenoH{r5} n j (by unfold M{r5}; omega) hn

theorem visitas_m3 (n : Nat) (hn : 3 ≤ n) : BuenoH n 1 :=
  buenoH{r3} n 1 (by unfold M{r3}; omega) (by omega)

theorem visitas_m1 (n : Nat) (hn : 2 ≤ n) : BuenoHUno n 0 :=
  buenoH{r1} n 0 (by unfold M{r1}; omega) (by omega)

end Hormiga
""")
open(os.path.join(RAIZ, 'lean/Hormiga/HerenciaCert.lean'), 'w').write('\n'.join(L))
print('hojas verificadas con U:', nhojas, ' nodos:', len(nodes))
