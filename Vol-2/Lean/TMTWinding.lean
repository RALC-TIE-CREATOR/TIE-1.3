/-
TIE — Linea 5 (TMT-E1), modulo 9: CONSERVACION DEL WINDING (entregable C1a) — PRIORIDAD 1.
Certifica la proteccion del lazo: el winding (entero) no cambia bajo el descenso discreto
mientras ninguna arista cruce un "phase slip" (salga de su banda), y es constante por continuidad.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- Contribucion de arista al winding: el entero mas proximo a `dphi/(2 pi)`, via `floor(x+1/2)`. -/
noncomputable def windTerm (dphi : ℝ) : ℤ := Int.floor (dphi / (2 * Real.pi) + 1 / 2)
/-- **C1a (sin phase slip)**: si dos incrementos de fase caen en la MISMA banda
    `[m-1/2, m+1/2)` de `dphi/(2 pi)` (ninguno cruza un medio-entero), su termino de
    winding es el mismo entero `m`. -/
theorem windTerm_eq_of_band {dphi dpsi : ℝ} {m : ℤ}
    (h1 : (m : ℝ) - 1 / 2 ≤ dphi / (2 * Real.pi)) (h2 : dphi / (2 * Real.pi) < (m : ℝ) + 1 / 2)
    (h3 : (m : ℝ) - 1 / 2 ≤ dpsi / (2 * Real.pi)) (h4 : dpsi / (2 * Real.pi) < (m : ℝ) + 1 / 2) :
    windTerm dphi = windTerm dpsi := by
  have e1 : windTerm dphi = m := by
    rw [windTerm, Int.floor_eq_iff]; exact ⟨by linarith, by linarith⟩
  have e2 : windTerm dpsi = m := by
    rw [windTerm, Int.floor_eq_iff]; exact ⟨by linarith, by linarith⟩
  rw [e1, e2]
/-- **C1a (proteccion del lazo)**: el winding de un lazo = suma de contribuciones de arista.
    Si bajo el descenso discreto cada termino se conserva (sin phase slips), el winding total
    es INVARIANTE. -/
theorem winding_invariant {n : ℕ} (dphi dpsi : Fin n → ℝ)
    (h : ∀ i, windTerm (dphi i) = windTerm (dpsi i)) :
    ∑ i, windTerm (dpsi i) = ∑ i, windTerm (dphi i) :=
  Finset.sum_congr rfl (fun i _ => (h i).symm)
/-- **C1a (constancia por continuidad)**: el winding es un entero; un cambio estrictamente
    menor que 1 no puede alterarlo (no hay continuo de enteros). -> invariante protegido. -/
theorem winding_const_of_no_slip {W0 Wt : ℤ} (h1 : -(1 : ℤ) < Wt - W0) (h2 : Wt - W0 < 1) :
    Wt = W0 := by omega
end TIE.TMT
