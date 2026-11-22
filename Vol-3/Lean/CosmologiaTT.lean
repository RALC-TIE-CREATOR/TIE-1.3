/-
TIE — Teoría del Tiempo (Cap. 1), paso T8: cosmología (TT23)
Identidades algebraicas de las ecuaciones de Friedmann en la TIE.

Se certifica (sin EDOs, solo álgebra exacta):
  · la densidad crítica despejada de la primera ecuación de Friedmann
    (TT23.1): `(8πG/3c²)·ρcrit = H²` ⟺ `ρcrit = 3c²H²/(8πG)`;
  · la continuidad del modo homogéneo con `w_φ = −1` (TT23.5): con `p_φ = −ρ_φ`
    la ecuación `ρ̇_φ + 3H(ρ_φ + p_φ) = 0` equivale a `ρ̇_φ = 0`;
  · el valor del modo homogéneo (TT23.6): `Ω_Λ = (4π+1)/(6π+1)` con `0 < Ω_Λ < 1`.

La derivación variacional completa (acción FLRW → EDOs) y la partición exacta
`Ω_b + Ω_c + Ω_Λ = 1` ya está cubierta por M3 (Cosmology.lean); aquí se añaden
las identidades escalares de TT23.
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TT23.6**: el parámetro del modo homogéneo `Ω_Λ = (4π+1)/(6π+1)`. -/
def OmegaLambda : ℝ := (4 * Real.pi + 1) / (6 * Real.pi + 1)

theorem OmegaLambda_pos : 0 < OmegaLambda := by
  have h1 : (0:ℝ) < 4 * Real.pi + 1 := by have := Real.pi_pos; positivity
  have h2 : (0:ℝ) < 6 * Real.pi + 1 := by have := Real.pi_pos; positivity
  unfold OmegaLambda; exact div_pos h1 h2

theorem OmegaLambda_lt_one : OmegaLambda < 1 := by
  have h2 : (0:ℝ) < 6 * Real.pi + 1 := by have := Real.pi_pos; positivity
  unfold OmegaLambda
  rw [div_lt_one h2]
  have := Real.pi_pos; linarith

/-- **TT23.1**: la densidad crítica despejada de la primera ecuación de Friedmann:
    `(8πG/3c²)·ρcrit = H²` con `ρcrit = 3c²H²/(8πG)`. -/
theorem friedmann_crit_identity (G c H : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) :
    8 * Real.pi * G / (3 * c^2) * (3 * c^2 * H^2 / (8 * Real.pi * G)) = H^2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **TT23.5**: continuidad del modo homogéneo con `w_φ = −1` (es decir `p_φ = −ρ_φ`):
    `ρ̇_φ + 3H(ρ_φ + p_φ) = 0` ⟺ `ρ̇_φ = 0`. -/
theorem wphi_continuity_zero (rhoDot rho H : ℝ) :
    rhoDot + 3 * H * (rho + (-rho)) = 0 ↔ rhoDot = 0 := by
  rw [add_neg_cancel, mul_zero, add_zero]

end TIE
