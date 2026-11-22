/-
TIE — Linea 5 (TMT-E1), modulo 16: INVARIANTES DEL MODELO DE 3 LAZOS (entregable E15).
Winding neto +-1 (protegido), cota E >= 3 E_core, conservacion del winding.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **E15**: el winding neto del barión = suma de 3 lazos (`±1` cada uno) -> NUNCA 0 (protegido). -/
theorem baryon_net_winding_ne_zero (w1 w2 w3 : ℤ)
    (h1 : w1 = 1 ∨ w1 = -1) (h2 : w2 = 1 ∨ w2 = -1) (h3 : w3 = 1 ∨ w3 = -1) :
    w1 + w2 + w3 ≠ 0 := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> decide
/-- **E15**: el winding neto es IMPAR (`±1` o `±3`) -> no puede deshacerse (protegido por topologia). -/
theorem baryon_net_winding_odd (w1 w2 w3 : ℤ)
    (h1 : w1 = 1 ∨ w1 = -1) (h2 : w2 = 1 ∨ w2 = -1) (h3 : w3 = 1 ∨ w3 = -1) :
    (w1 + w2 + w3) % 2 ≠ 0 := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> decide
/-- **E15 (cota inferior)**: `E = 3 E_core + E_int`, `E_int >= 0` -> `E >= 3 E_core`. -/
theorem E_baryon_lower_bound {Ecore Eint : ℝ} (h : 0 ≤ Eint) : 3 * Ecore ≤ 3 * Ecore + Eint := by
  linarith
/-- **E15**: conservación del winding (sin phase slips) — misma ley que `TMTWinding`. -/
theorem baryon_winding_conserved {W0 Wt : ℤ} (h1 : -(1 : ℤ) < Wt - W0) (h2 : Wt - W0 < 1) :
    Wt = W0 := by omega
end TIE.TMT
