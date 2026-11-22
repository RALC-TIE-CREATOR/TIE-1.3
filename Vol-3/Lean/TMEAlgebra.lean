/-
TIE — Electrodinámica (Cap. 8, TME): paso TME1 (BARRIDO_TME_LEAN.md)

Aritmética limpia del capítulo:
  (a) **C_lat = π²/12** con cota de intervalo (π acotado a 6 dígitos) — pasa de
      «parámetro de parametrización» a valor certificado (V2);
  (b) **factor 2 de la fuente gravitacional EM**: de ρ_em + 3p_em/c² con
      p_em = u_em/3 se obtiene la fuente 2u_em/c² (V5).

El resto del capítulo es física/retícula; ver el barrido (A08-01..A08-07).
La dispersión fotónica de red (V4) ya está cubierta por Espacio (E2).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TME1 (C_lat)**: `π²/12 ∈ (0.8224, 0.8225)` — el coeficiente de retícula
    queda certificado, no parametrizado. -/
theorem clat_value :
    (0.8224:ℝ) < Real.pi^2 / 12 ∧ Real.pi^2 / 12 < 0.8225 := by
  have hp := Real.pi_pos
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hp2 : (3.141592:ℝ)^2 < Real.pi^2 := by nlinarith [h1, hp]
  have hq2 : Real.pi^2 < (3.141593:ℝ)^2 := by nlinarith [h2, hp]
  constructor
  · nlinarith [hp2]
  · nlinarith [hq2]

/-- **TME1 (factor 2 de la fuente EM)**: `ρ_em + 3p_em/c² = 2 u_em/c²` para el
    campo EM estático, con `p_em = u_em/3`. -/
theorem em_source_factor (u c : ℝ) (hc : c ≠ 0) :
    u / c^2 + 3 * ((u / 3) / c^2) = 2 * u / c^2 := by
  ring_nf

end TIE
