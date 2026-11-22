/-
TIE — Linea 5 (TMT-E1), modulo 8: CAMPO DEL PAR (entregables B3, B4, B5, B5b).
Incluye la peticion Lean explicita de B5b: conservacion del winding sin phase slips + cota E(d) >= 2 E_core.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/- **B4**: clases del par (a1,a2,L) con a1,a2 in {x,y,z}, L in {-1,0,+1}.
   Crudas 3*3*3 = 27; cociente por q<->qbar (Burnside): fijos = a1=a2 y L=0. -/
theorem pair_raw : 3 * 3 * 3 = 27 := by decide
/-- **B4 (fijos de `q↔q̄`)**: estados `(a1,a2,L)` con `a1=a2` y `L=0` — codificando cada
    índice en `Fin 3` (para `L`, el índice `1` representa `L=0`): **3** estados fijos. -/
theorem pair_fixed_by_swap :
    (Finset.univ.filter (fun s : Fin 3 × Fin 3 × Fin 3 =>
      s.1 = s.2.1 ∧ s.2.2 = (1 : Fin 3))).card = 3 := by decide
/-- **B4 (Burnside q<->qbar)**: orbitas = (27 + 3) / 2 = **15**. -/
theorem pair_orbits : (27 + 3) / 2 = 15 := by decide
/-- **B4 (NEGATIVO)**: el conteo natural de clases del par (15, o 12 relativas) NO es C (7, 13). -/
theorem pair_classes_ne_C : (15 : ℕ) ≠ 7 ∧ (15 : ℕ) ≠ 13 ∧ (12 : ℕ) ≠ 13 := by decide
/-- **B5b (peticion Lean) — conservacion del winding (sin phase slips)**:
    el winding es ENTERO; un cambio estrictamente menor que 1 no puede cambiar su valor. -/
theorem winding_no_slip {W0 Wt : ℤ} (h1 : -(1 : ℤ) < Wt - W0) (h2 : Wt - W0 < 1) : Wt = W0 := by
  omega
/-- **B5b (peticion Lean) — cota inferior**: si `E(d) = 2 E_core + E_int(d)` con `E_int(d) >= 0`
    (energia de interaccion no negativa), entonces `E(d) >= 2 E_core`. -/
theorem E_pair_lower_bound {Ecore Eint : ℝ} (h : 0 ≤ Eint) : 2 * Ecore ≤ 2 * Ecore + Eint := by
  linarith
/- **B5b (correccion, hallazgo numerico del equipo)**: la minimizacion RELAJADA muestra un plateau
   (interaccion de corto alcance), retirando la lectura de confinamiento lineal (`sigma d`) de B5.
   Es un resultado NUMERICO del equipo; no se certifica aqui (no hay teorema que lo afirme). -/
end TIE.TMT
