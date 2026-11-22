/-
B4 — TMT13: normalización kR del nudo toroidal.
Carpeta: tie-review/teoria-abierta/B4-TMT13-kR/
Resultado: kR = s/(2π(2+r²)) es GEOMÉTRICO; kR = 1/2 exige s = π(2+r²), que la tabla TMT13
no satisface (s es 16–28% mayor). El «1/2» de PD-T1 es la normalización de espín, no la geométrica.
-/
import Mathlib
namespace TIE.B4
/-- `kR` geométrico del nudo toroidal: `kR = s/(2π(2+r²))`. -/
noncomputable def kR (s r : ℝ) : ℝ := s / (2 * Real.pi * (2 + r^2))
/-- **B4 — condición exacta para la normalización «media»**: `kR = 1/2 ↔ s = π(2+r²)`. -/
theorem kR_half_iff (s r : ℝ) (h : 2 + r^2 ≠ 0) :
    kR s r = 1/2 ↔ s = Real.pi * (2 + r^2) := by
  unfold kR
  constructor
  · intro hh
    field_simp at hh
    linarith
  · intro hh
    rw [hh]
    field_simp
/-- **B4 — positividad**: con `s > 0`, `kR > 0`. -/
theorem kR_pos (s r : ℝ) (hs : 0 < s) : 0 < kR s r := by
  unfold kR
  positivity
end TIE.B4
