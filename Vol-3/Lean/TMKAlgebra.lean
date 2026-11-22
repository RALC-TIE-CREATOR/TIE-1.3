/-
TIE — Cosmología (Cap. 9, TMK): paso TMK1 (BARRIDO_TMK_LEAN.md)

Aritmética de Λ y H₀:
  (a) **H₀ = 1/t_U → 70.88 km/s/Mpc** (t_U = 4.354×10¹⁷ s; 1 Mpc = 3.0857×10¹⁹ km);
  (b) **Λ ↔ H₀**: `3Ω_Λ/(c²t_U²) = 3Ω_Λ(1/t_U)²/c²`.

El resto del capítulo (redshift, gravedad modificada TC5, perturbaciones,
bariogénesis) ya está mayormente cubierto por M3/M7 o es física; ver el barrido
(A09-01..A09-08). Con esto se cierra el barrido del libro (caps. 1–9).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TMK1 (H₀ = 1/t_U en km/s/Mpc)**: con `t_U = 4.354×10¹⁷ s` y
    `1 Mpc = 3.0857×10¹⁹ km`, la tasa queda en `(70.8, 70.9)` km/s/Mpc. -/
theorem hubble_value :
    (70.8:ℝ) < ((4.354e17 : ℝ))⁻¹ * (3.0857e19 : ℝ) ∧
      ((4.354e17 : ℝ))⁻¹ * (3.0857e19 : ℝ) < 70.9 := by
  constructor <;> norm_num

/-- **TMK1 (Λ en función de H₀)**: `3Ω_Λ/(c²t_U²) = 3Ω_Λ·(1/t_U)²/c²` (con H₀ = 1/t_U). -/
theorem lambda_in_hub (omegaL c tU : ℝ) (hc : c ≠ 0) (htU : tU ≠ 0) :
    3 * omegaL / (c^2 * tU^2) = 3 * omegaL * (1 / tU)^2 / c^2 := by
  field_simp

/-- **TMK1 (V1.3)**: valor autoconsistente `H0 = F/t_mat` con `t_mat = 13.80 Gyr`, `F = 0.9496`,
    en `(67.2, 67.4)` km/s/Mpc. (El `70.88` de `hubble_value` usa la edad de Friedmann de LambdaCDM
    y es el artefacto retirado por D-2(i): obs:Teo1_verificacion.) -/
theorem hubble_value_autoconsistente :
    (67.2:ℝ) < (9496/10000 : ℝ) / (1380/100) * 1000 * (30857/10000) / (3156/1000) ∧
      (9496/10000 : ℝ) / (1380/100) * 1000 * (30857/10000) / (3156/1000) < 67.4 := by
  constructor <;> norm_num

end TIE
