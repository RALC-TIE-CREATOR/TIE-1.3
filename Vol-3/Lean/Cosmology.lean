/-
TIE M3 — Fracciones cosmológicas (cap. 9, TMK: partición TC10)
La partición geométrica: Ω_b = 1/(6π+1), Ω_c = (2π−1)/(6π+1), Ω_Λ = (4π+1)/(6π+1).
Verificación: Mathlib (field_simp/ring/norm_num).
-/
import Mathlib

namespace TIE

/-! ## La partición de TC10 -/

noncomputable def OmegaB : ℝ := 1/(6*Real.pi + 1)
noncomputable def OmegaC : ℝ := (2*Real.pi - 1)/(6*Real.pi + 1)
noncomputable def OmegaL : ℝ := (4*Real.pi + 1)/(6*Real.pi + 1)

/-- La partición suma exactamente 1 (1 + (2π−1) + (4π+1) = 6π+1). -/
theorem omega_sum : OmegaB + OmegaC + OmegaL = 1 := by
  unfold OmegaB OmegaC OmegaL
  have h : (6:ℝ)*Real.pi + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- La identidad de los numeradores. -/
theorem omega_numeradores :
    (1 + (2*Real.pi - 1) + (4*Real.pi + 1) : ℝ) = 6*Real.pi + 1 := by ring

/-- Los pesos geométricos: 1, 2π−1, 4π+1. -/
theorem omega_pesos :
    (1:ℝ) + (2*Real.pi - 1) = 2*Real.pi ∧ (2*Real.pi) + (4*Real.pi + 1) = 6*Real.pi + 1 :=
  ⟨by ring, by ring⟩

/-! ## Cotas numéricas elementales (π > 3, π < 4) -/

/-- Con π > 3: 6π+1 > 19 → Ω_b = 1/(6π+1) < 1/19. -/
theorem omegaB_menor (hpi : (3:ℝ) < Real.pi) : OmegaB < 1/19 := by
  unfold OmegaB
  apply one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 19)
  nlinarith

/-- Con 0 < π < 4: 6π+1 < 25 → 1/25 < Ω_b. -/
theorem omegaB_mayor (hpi : Real.pi < 4) (hpi0 : 0 < Real.pi) : 1/25 < OmegaB := by
  unfold OmegaB
  apply one_div_lt_one_div_of_lt (by nlinarith : (0:ℝ) < 6*Real.pi + 1)
  nlinarith

end TIE
