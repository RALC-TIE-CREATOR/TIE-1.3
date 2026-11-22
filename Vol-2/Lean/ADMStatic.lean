/-
TIE — Lean-ADM-01 (Capa 10): identidades algebraicas del sector ESTÁTICO.
Del ec. de variación de h_ij (N R_ij + h_ij ΔN - ∇_i∇_j N = 0) con R^(3)=0:
traza (dim 3) => ΔN=0 ; luego R^(3)_ij = N^{-1} ∇_i∇_j N.
-/
import Mathlib
namespace TIE
/-- **Lean-ADM-01 (traza)**: con `R^(3)=0`, la traza (dim 3) del ec. de variación estática
    da `Δ_h N = 0` (pues tr h = 3 y tr(∇∇N) = ΔN, y tr R = 0). -/
theorem static_trace_deltaN_zero (dN : ℝ) (h : 3 * dN - dN = 0) : dN = 0 := by linarith
/-- **Lean-ADM-01**: de `N R^{(3)}_{ij} = ∇_i∇_j N` (tras ΔN=0) se despeja
    `R^{(3)}_{ij} = N^{-1} ∇_i∇_j N`. -/
theorem static_solve_Rij (N Rij lapN : ℝ) (hN : N ≠ 0) (h : N * Rij = lapN) :
    Rij = lapN / N := by
  rw [eq_div_iff hN, mul_comm Rij N]; exact h
end TIE
