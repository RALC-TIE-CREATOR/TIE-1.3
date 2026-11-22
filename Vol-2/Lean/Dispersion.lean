/-
TIE M8 — Dispersión de red (TE-red): la serie truncada

ω = c·k·(1 − (a₀²/24)·Σ kᵢ⁴/k² + …)

Se certifican las identidades algebraicas del desarrollo:
  · el coeficiente 1/24 surge del producto (1/2)·(1/12) — el 1/2 de la raíz
    (√(1−u) ≈ 1 − u/2) y el 1/12 de la expansión del seno (sen²x = x² − x⁴/3 + …);
  · el coeficiente 1/6 es 4·(1/24) (el puente entre ω y 4·Σ sen²(kᵢa/2)).

Todo sobre ℚ por `ring`/`field_simp`/`norm_num`.
-/
import Mathlib

namespace TIE

/-- Serie truncada de la dispersión de red (primer orden en a²). -/
def truncOmega (a c k S : ℚ) : ℚ := c * k * (1 - (a^2 * S) / 24)

/-- El coeficiente 1/24 del desarrollo: (1/2)·(1/12). -/
theorem coef_1_24 : (1/2 : ℚ) * (1/12) = 1/24 := by norm_num

/-- El coeficiente 1/6 es 4·(1/24) (puente entre ω y 4·Σ sen²). -/
theorem coef_1_6 : (4 : ℚ) * (1/24) = 1/6 := by norm_num

/-- La forma factorizada: ω = c·k·(1 − (1/2)·(a²/12)·S). -/
theorem truncOmega_factor (a c k S : ℚ) :
    truncOmega a c k S = c * k * (1 - (1/2) * (a^2 / 12) * S) := by
  unfold truncOmega; ring

/-- Forma desarrollada: ω = c·k − (c·k·a²/24)·S. -/
theorem truncOmega_expand (a c k S : ℚ) :
    truncOmega a c k S = c * k - (c * k * a^2 / 24) * S := by
  unfold truncOmega; ring

/-- Corrección relativa de primer orden: (ω − c·k)/(c·k) = −(a²/24)·S. -/
theorem truncOmega_correction (a c k S : ℚ) (hc : c ≠ 0) (hk : k ≠ 0) :
    (truncOmega a c k S - c * k) / (c * k) = -(a^2 * S) / 24 := by
  unfold truncOmega
  field_simp
  ring

end TIE
