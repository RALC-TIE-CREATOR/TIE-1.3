/-
B2 — TC10a: pesos topológicos y las normalizaciones forzadas.
Carpeta: tie-review/teoria-abierta/B2-TC10a-pesos/
Resultado: las "dos normalizaciones libres" (a=1.297, R=6.783) NO son libres: son la solución
única de pi a^2 = 2pi-1 y 2R = 4pi+1. Pero implican r = a/R = 0.1912, incompatible con el
r = 0.50487 certificado para w_p=2 (TMT13) => la lectura Hausdorff queda refutada como derivación.
-/
import Mathlib
namespace TIE.B2
/-- **B2 — suma de pesos**: `1 + (2π−1) + (4π+1) = 6π+1`. -/
theorem weight_sum : 1 + (2 * Real.pi - 1) + (4 * Real.pi + 1) = 6 * Real.pi + 1 := by ring
/-- **B2 — normalización**: las tres fracciones suman 1. -/
theorem frac_sum (h : 6 * Real.pi + 1 ≠ 0) :
    1 / (6 * Real.pi + 1) + (2 * Real.pi - 1) / (6 * Real.pi + 1)
      + (4 * Real.pi + 1) / (6 * Real.pi + 1) = 1 := by
  field_simp
  ring
/-- **B2 — `a` forzado**: `πa² = 2π−1 ↔ a² = 2 − 1/π` (la normalización no es libre). -/
theorem a_forced (a : ℝ) (hpi : Real.pi ≠ 0) :
    Real.pi * a^2 = 2 * Real.pi - 1 ↔ a^2 = 2 - 1 / Real.pi := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith
/-- **B2 — `R` forzado**: `2R = 4π+1 ↔ R = (4π+1)/2`. -/
theorem R_forced (R : ℝ) : 2 * R = 4 * Real.pi + 1 ↔ R = (4 * Real.pi + 1) / 2 := by
  constructor <;> intro h <;> linarith
end TIE.B2
