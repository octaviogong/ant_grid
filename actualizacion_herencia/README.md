# Highways of the RⁿLᵐ ants from the blank grid

Code, data and formal proofs for the paper *Highways of the RⁿLᵐ ants from the blank grid: a formally
verified period law* (in preparation).

**Main results.** For every odd m ≥ 3 and n ≥ m − 1 (n ≥ 3 when m = 3), except (n, m) = (12, 13), the
generalised Langton ant RⁿLᵐ started on the blank grid enters, within 204·(n + m) steps, a highway of period
16(n + m) − 20. The ant RⁿL enters a highway of period 16n + 4 within 40·(n + 1) steps for every n ≥ 2.
Both theorems are proved in Lean 4 (`lean/`).

**Prefix inheritance.** Let m be odd, n ≥ m (or m = 1 and n ≥ 2), and K = 2n + m + 1. Every rule whose first
K letters are RⁿLᵐRⁿL, whatever its length and its remaining letters, follows from the blank grid exactly the
same trajectory as RⁿLᵐ, so it builds the same highway at the same step. Proved in Lean 4
(`lean/Hormiga/HerenciaTeorema.lean`, theorems `herencia`, `herencia_RnL`, `herencia_palabra`); see `herencia/`.

## Repository layout

| Folder | Contents |
|---|---|
| `lean/` | Lean 4 development (no Mathlib, no `sorry`): the model, the repetition and loop lemmas, a symbolic certificate checker proved sound, the 42 certificates, the case tree and the final theorems `ley_m5`, `ley_m3`, `ley_RnL`; also Langton's ant, the exception (12, 13) and the 12 non-diagonal highways. See `lean/LEEME.md`. |
| `prueba/` | The Python search engine that *finds* the certificates (symbolic execution with affine forms, loop acceleration, case splitting) and exports them to Lean (`exporta.py`, `gen_lean.py`). Proof notes in `prueba/DEMOSTRACION.md`. Python is not part of the trusted base. |
| `herencia/` | The prefix-inheritance theorem: statement and proof outline (`LEEME.md`), a Python replica of the lifted checker, and the generators of `SimbolicoU.lean` and `HerenciaCert.lean`. |
| `semillas/` | Experiments on chaotic transients (Section 6 of the paper): waiting times from random boards, robustness under three initial conditions, seed sizes. |
| `exploracion/` | Earlier exploratory work: the rule catalogue of all 4,083 rules with 2–12 states (`pendientes.json`), tori, higher dimensions. `exploracion/angulos/`: rules as codings of a rotation angle (golden angle, Fibonacci word), highway "tongues" around α = 1/(n+1), torus cover times. |

Most notes inside the folders are in Spanish.

## Reproducing

**Formal proofs** (about one minute; the inheritance certificates are regenerated with `python3 herencia/gen_simbolicoU.py && python3 herencia/gen_herencia.py`):
```bash
cd lean
lake build                               # needs elan: https://lean-lang.org/install/
lake env lean Hormiga/Verificacion.lean  # prints the statements and the axioms they use
```
The checks rely on Lean's kernel plus `native_decide` for evaluating certificates (one axiom per
certificate, listed by `#print axioms`); see `lean/LEEME.md` for details.

**Search engine and experiments** (Python 3 with numpy and scipy, and gcc):
```bash
cd prueba && python3 exporta.py m5 m3 m1 && python3 gen_lean.py native_decide   # regenerates lean/Hormiga/Certificados.lean
cd semillas && python3 experimento.py && python3 robustez.py && python3 robustez_analisis.py   # several hours
```

## Citation

If you use this material, please cite the paper (reference to be added on publication).
