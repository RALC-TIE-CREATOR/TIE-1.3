/-
TIE — Lean-ADM-02 (Capa 10): curvatura extrínseca linealizada con shift retenido
K^{(1)}_{ij} = 1/(2c)(γ̇_ij - ∂_iν_j - ∂_jν_i), ν_i ≡ N_i ; su simetría (para γ simétrica)
y la restricción de momento (que en el sector transversal da la E-10: V̇^T = N^T).
-/
import TieFormal.TT19Shift
import Mathlib
namespace TIE
/-- **Lean-ADM-02**: con `γ̇` simétrico (`gdij = gdji`), `K^{(1)}_{ij}` es simétrico. -/
theorem K1_symmetric (c gdij gdji diNj djNi : ℝ) (hgd : gdij = gdji) :
    (1/(2*c)) * (gdij - diNj - djNi) = (1/(2*c)) * (gdji - diNj - djNi) := by
  rw [hgd]
/-- **Lean-ADM-02 (consecuencia de la variación en ν_i)**: la restricción de momento
    fija, en el sector transversal, `∇^2(V̇^T - N^T)=0` ⇒ `V̇^T = N^T` (E-10). -/
theorem shift_momentum_constraint (k Vdot N : ℝ) (hk : k ≠ 0)
    (h : k^2 * (Vdot - N) = 0) : Vdot = N :=
  vector_velocity_fixed k Vdot N hk h
end TIE
