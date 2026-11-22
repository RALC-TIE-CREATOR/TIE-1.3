/-
TIE — Lean-GW-01 (Capa 10): de □γ^TT_ij = 0 (□ = -c^{-2}∂_t^2 + ∇^2) sobre una onda
plana, la relación de dispersión es ω^2 = c^2 k^2 (velocidad de fase/grupo c).
-/
import Mathlib
namespace TIE
/-- **Lean-GW-01**: `□γ = (k^2 - ω^2/c^2)·A = 0` con amplitud `A ≠ 0` ⇒ `ω^2 = c^2 k^2`. -/
theorem TT_dispersion (c ω k A : ℝ) (hc : c ≠ 0) (hA : A ≠ 0)
    (h : (k^2 - ω^2 / c^2) * A = 0) : ω^2 = c^2 * k^2 := by
  have h0 : k^2 - ω^2 / c^2 = 0 := (mul_eq_zero.mp h).resolve_right hA
  have h1 : k^2 = ω^2 / c^2 := sub_eq_zero.mp h0
  rw [eq_div_iff (pow_ne_zero 2 hc)] at h1
  rw [← h1, mul_comm]
/-- **Lean-GW-01 (corolario)**: velocidad de fase `v = ω/k = c`. -/
theorem TT_phase_velocity (c ω k : ℝ) (hk : k ≠ 0) (h : ω^2 = c^2 * k^2) :
    (ω / k)^2 = c^2 := by
  rw [div_pow, h]
  rw [mul_div_assoc, div_self (pow_ne_zero 2 hk), mul_one]
end TIE
