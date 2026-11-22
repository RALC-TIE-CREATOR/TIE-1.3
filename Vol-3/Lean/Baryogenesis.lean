/-
TIE M7 — Bariogénesis y Λ (cap. 9, TMK)
Las cadenas: η = 7.04·δ_CP·(g_B/g_*)·(T_dec/T_*)³ y Λ = 3(4π+1)/(6π+1)/(c²t_U²).
Verificación: Mathlib (ring/field_simp/norm_num).
-/
import Mathlib

namespace TIE

noncomputable def OmegaL' : ℝ := (4*Real.pi + 1)/(6*Real.pi + 1)

/-! ## El factor de conversión de entropía -/

/-- s/n_γ = 7.04 = 176/25 (exacto). -/
theorem s_sobre_ngamma : (7.04:ℝ) = 176/25 := by norm_num

/-- La fracción de quarks g_B = 72 = 6 × 12. -/
theorem g_B_value : (72:ℕ) = 6 * 12 := rfl

/-- La relación de dof: 72/106.75 = 288/427 (exacto). -/
theorem g_ratio : (72:ℝ)/(106.75) = 288/427 := by norm_num

/-! ## La asimetría bariónica (estructura) -/

/-- η estructural: (s/n_γ)·δ_CP·(g_B/g_*)·(T_dec/T_*)³. -/
noncomputable def etaEstructura (deltaCP gB gstar Tdec Tstar : ℝ) : ℝ :=
  (176/25) * deltaCP * (gB/gstar) * (Tdec/Tstar)^3

/-- Con los valores declarados, los factores se combinan. -/
theorem eta_combinada (Tdec Tstar : ℝ) :
    etaEstructura (Real.pi/6) 72 106.75 Tdec Tstar =
    (176/25) * (Real.pi/6) * (288/427) * (Tdec/Tstar)^3 := by
  unfold etaEstructura
  rw [g_ratio]

/-- El factor numérico combinado (sin T): 8448/10675. -/
theorem eta_factor_estructura :
    (176/25) * (1/6) * (288/427) = 8448/10675 := by norm_num

/-! ## La constante cosmológica (estructura) -/

/-- Λ = 3(4π+1)/(6π+1)/(c²t_U²): sin parámetros libres adicionales. -/
noncomputable def LambdaEstructura (c tU : ℝ) : ℝ :=
  3*(4*Real.pi + 1)/(6*Real.pi + 1)/(c^2*tU^2)

/-- La forma multiplicativa de la misma cadena: Λ = 3·Ω_Λ/(c²t_U²). -/
theorem Lambda_como_OmegaL (c tU : ℝ) :
    LambdaEstructura c tU = 3 * OmegaL' / (c^2*tU^2) := by
  unfold LambdaEstructura OmegaL'
  ring

/-- H₀ = 1/t_U (el conteo de ticks del horizonte). -/
noncomputable def H0_horizonte (tU : ℝ) : ℝ := 1/tU

/-- La consistencia de H₀: H₀·t_U = 1 (para t_U ≠ 0). -/
theorem H0_consistencia (tU : ℝ) (ht : tU ≠ 0) :
    H0_horizonte tU * tU = 1 := by
  unfold H0_horizonte
  field_simp

end TIE
