/-
B1 + B5 — cadena cinemática de la rigidez de la red.
Carpeta: tie-review/teoria-abierta/B1-TC5a-2pi/RIGIDEZ_DESDE_ACCION.md
Resultado: a_lat = c/T0 = a0/T0^2 (saturación) = c*omega0/(2pi); a_tr = a_lat/(2πn) = c*H0/(2π)
con H0 = 1/(n*T0). Sin coeficiente libre. Además beta = gamma por la definición de x = g/a_tr.
-/
import Mathlib
namespace TIE.B1B5
/-- **B1+B5 — paso 1→2**: con `c = a₀/T₀`, la aceleración de saturación `a₀/T₀²` es `c/T₀`. -/
theorem alat_kinematic (a0 T0 c : ℝ) (hT : T0 ≠ 0) (hc : c = a0 / T0) :
    a0 / T0^2 = c / T0 := by
  subst hc
  field_simp
/-- **B1+B5 — paso 3**: con `ω₀ = 2π/T₀`, `a_lat = c·ω₀/(2π)` (el `2π` es la fase de un tick). -/
theorem alat_phase_form (a0 T0 c ω0 : ℝ) (hT : T0 ≠ 0)
    (hc : c = a0 / T0) (hω : ω0 = 2 * Real.pi / T0) :
    a0 / T0^2 = c * ω0 / (2 * Real.pi) := by
  rw [hc, hω]
  field_simp
/-- **B1+B5 — paso 4**: `a_tr = a_lat/(2πn)` es `c·H₀/(2π)` con `H₀ = 1/(nT₀)`. -/
theorem atr_H0_form (c T0 n : ℝ) (hT : T0 ≠ 0) (hn : n ≠ 0) :
    c / (2 * Real.pi * n * T0) = c * (1 / (n * T0)) / (2 * Real.pi) := by
  field_simp
/-- **B5 — `β = γ`**: si en la transición (`x = 1`) la ocupación es `1/2`, el equilibrio
`β(1−½) = γ(½)` obliga `β = γ` (no es un ajuste). -/
theorem beta_eq_gamma (β γ : ℝ) (h : β * (1 - 1/2) = γ * (1/2)) : β = γ := by
  linarith
/-- **B1+B5 — positividad** de la aceleración de saturación. -/
theorem alat_pos (a0 T0 : ℝ) (ha : 0 < a0) (hT : 0 < T0) : 0 < a0 / T0^2 := by
  positivity
end TIE.B1B5
