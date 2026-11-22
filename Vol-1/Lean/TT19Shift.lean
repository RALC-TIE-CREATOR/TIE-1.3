/-
TIE — TT19 con N^i (E-10): la restriccion de momento fija el sector vectorial.
nabla^2(Vdot_i^T - N_i^T) = 0; sin armonicas (k != 0) fija Vdot_i^T = N_i^T.
-/
import Mathlib

namespace TIE

/-- **E-10**: `k^2 * X = 0` con `k != 0` implica `X = 0` (restriccion de momento por modo). -/
theorem momentum_constraint_mode (k X : ℝ) (hk : k ≠ 0) (h : k^2 * X = 0) : X = 0 := by
  have hk2 : k^2 ≠ 0 := pow_ne_zero 2 hk
  exact (mul_eq_zero.mp h).resolve_left hk2

/-- **E-10**: la restriccion fija la velocidad del vector: `Vdot = N` en el modo `k != 0`. -/
theorem vector_velocity_fixed (k Vdot N : ℝ) (hk : k ≠ 0) (h : k^2 * (Vdot - N) = 0) :
    Vdot = N := by
  have h0 := momentum_constraint_mode k (Vdot - N) hk h
  linarith

end TIE
