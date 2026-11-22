/-
TIE — F3 (cierre del gap V1.3): bloque estructural TMT/TMK.
Protocolo v1.0: cada teorema cita la etiqueta y declara su gap.

GAPS CONOCIDOS (auditoría 2026-10-31 → 2026-11-04): cada teorema declara su gap (G5) en el
docstring; la tabla canónica está en README.md y el detalle por ítem en REGISTRO_CIERRE_GAP.csv.
-/
import Mathlib
namespace TIE
/-- **TMT · radio mayor de confinamiento**: de `R = kR·ħ/(m c)` se sigue `m·R = kR·(ħ/c)`
    (la relación masa-radio que usa LM1).
    Gap declarado (Gap 5): identidad algebraica; la normalización `kR` (0.6405 vs 1/2) es
    una elección de modelo (TMT13, pendiente en el corpus). -/
theorem tmt_radius_relation (kR hbar m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    (kR * hbar / (m * c)) * m = kR * (hbar / c) := by
  field_simp
/-- **TMK-TC2c (dilatación temporal de Supernovas Tipo Ia)**: con `Δt_obs = (1+z)·Δt_emit`,
    el cociente de duraciones observada/emitida es exactamente `1+z`.
    Gap declarado (Gap 5): álgebra de la relación del texto; el ajuste a datos de SN Ia no se
    formaliza. -/
theorem tmk_tc2c_dilation (z dtObs dtEmit : ℝ) (hE : dtEmit ≠ 0)
    (h : dtObs = (1 + z) * dtEmit) : dtObs / dtEmit = 1 + z := by
  rw [h]
  field_simp
/-- **TMK-TC5 (escala de transición `a_tr`)**: con `a_tr = c/(2π t_U)` y `H₀ = 1/t_U`, se sigue
    `a_tr = c·H₀/(2π)`.
    Gap declarado (Gap 5): vínculo ALGEBRAICO entre las tres formas; la derivación del factor
    `1/(2π)` desde la acción/red sigue **ABIERTA** (TMK-TC5a, declarado en el corpus). -/
theorem tc5_atr_identity (c tU H0 : ℝ) (ht : tU ≠ 0) (hh : H0 = 1 / tU) :
    c / (2 * Real.pi * tU) = c * H0 / (2 * Real.pi) := by
  rw [hh]
  field_simp
end TIE
