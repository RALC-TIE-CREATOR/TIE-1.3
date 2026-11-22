/-
B5 — mu(x) desde la estadística de renovación (equilibrio llenado/vaciado).
Carpeta: tie-review/teoria-abierta/B5-mu-x-renovacion/
Resultado: con llenado ~ x^p (1-n) y vaciado ~ n, el equilibrio da n = x^p/(1+x^p);
para p=2 y mu = sqrt(n) se obtiene EXACTAMENTE mu = x/sqrt(1+x^2) (la forma adoptada).
-/
import Mathlib
namespace TIE.B5
/-- **B5 — equilibrio de renovación, caso p=1 (Langmuir)**: `x(1−n) = n` con `n = x/(1+x)`. -/
theorem langmuir_equilibrium (x : ℝ) (h : 1 + x ≠ 0) :
    x * (1 - x / (1 + x)) = x / (1 + x) := by
  field_simp
  ring
/-- **B5 — equilibrio de renovación, caso p=2 (par de ticks)**: `x²(1−n) = n` con `n = x²/(1+x²)`. -/
theorem pair_equilibrium (x : ℝ) (h : 1 + x^2 ≠ 0) :
    x^2 * (1 - x^2 / (1 + x^2)) = x^2 / (1 + x^2) := by
  field_simp
  ring
/-- **B5 — μ = √n**: con `n = x²/(1+x²)`, la raíz es `x/√(1+x²)` (la forma adoptada por el corpus). -/
theorem mu_sq_from_occupancy (x : ℝ) (hx : 0 ≤ x) :
    (x / Real.sqrt (1 + x^2))^2 = x^2 / (1 + x^2) := by
  have h1 : (0:ℝ) < 1 + x^2 := by positivity
  rw [div_pow, Real.sq_sqrt (le_of_lt h1)]
/-- **B5 — no negatividad** de `μ` en el dominio físico. -/
theorem mu_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x / Real.sqrt (1 + x^2) := by positivity
/-- **B5 — saturación**: `μ ≤ 1` (régimen newtoniano). -/
theorem mu_le_one (x : ℝ) (hx : 0 ≤ x) : x / Real.sqrt (1 + x^2) ≤ 1 := by
  have h1 : (0:ℝ) < 1 + x^2 := by positivity
  have hs : (0:ℝ) < Real.sqrt (1 + x^2) := Real.sqrt_pos.2 h1
  rw [div_le_one hs]
  calc x = Real.sqrt (x^2) := by rw [Real.sqrt_sq hx]
    _ ≤ Real.sqrt (1 + x^2) := Real.sqrt_le_sqrt (by linarith)
/-- **B5 — valor en la transición**: `μ(1) = 1/√2`. -/
theorem mu_at_one : (1:ℝ) / Real.sqrt (1 + 1^2) = 1 / Real.sqrt 2 := by norm_num
end TIE.B5