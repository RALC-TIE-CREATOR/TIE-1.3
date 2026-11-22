/-
TIE — Gravitación No Lineal (Cap. 6, TMG): paso TMG1 (BARRIDO_TMG_LEAN.md)

Identidad exacta de la densidad máxima (V3, TMG-cosmo):
  ρ_max = ℏc/a₀⁴ = ρ_Planck/(4π²),
con  a₀² = 2π·ℓ_P²,  ℓ_P² = ℏG/c³,  ρ_Planck = c⁷/(ℏG²).

El resto del capítulo (TG1–TG9) es física/construcción; ver el barrido para los
caveats A06-01..A06-07 (en particular A06-03: el signo de Lense-Thirring, ligado
a la decisión del signo del Sagnac D9).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TMG1 (densidad máxima)**: `ℏc/a₀⁴ = ρ_Planck/(4π²)` con `a₀² = 2π·(ℏG/c³)`
    y `ρ_Planck = c⁷/(ℏG²)`. -/
theorem rho_max_planck (hbar c G : ℝ) (hh : hbar ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    hbar * c / (2 * Real.pi * (hbar * G / c^3))^2
      = (c^7 / (hbar * G^2)) / (4 * Real.pi^2) := by
  field_simp
  ring

end TIE
