/-
B1 — TC5a: explicación física del factor 1/(2π) anclada en definiciones CERTIFICADAS.
Carpeta: tie-review/teoria-abierta/B1-TC5a-2pi/
Anclas certificadas (Primitivos.lean / F1QuickWins.lc1_phase_locked):
  · c = a0/T0            (Primitivos.c)
  · omega0 = 2π/T0       (Primitivos.omega0)
  · E0 = πħ/T0 = ħω0/2   (Primitivos.E0)
  · fase por tick = 2πn  (LC1: φ = 2πn·ω/ω0)
Estado: explicación física (no derivación desde la acción); TC5a sigue abierto como derivación.
-/
import Mathlib
namespace TIE.B1
/-- **B1 — forma-circunferencia**: con `H = c/R_H`, `a_tr = cH/(2π) = c²/(2πR_H) = c²/C_H`
    (circunferencia de Hubble): el `1/(2π)` es la conversión radio → circunferencia. -/
theorem tc5_circumference_form (c R H : ℝ) (hH : H = c / R) (hR : R ≠ 0) (hc : c ≠ 0) :
    c * H / (2 * Real.pi) = c^2 / (2 * Real.pi * R) := by
  rw [hH]
  field_simp
/-- **B1 — unicidad dimensional**: toda aceleración construida con `c,H` es `κ·cH`. -/
theorem atr_dimensional_form (c H a : ℝ) (hc : c ≠ 0) (hH : H ≠ 0) :
    ∃ κ : ℝ, a = κ * (c * H) := ⟨a / (c * H), by field_simp⟩
/-- **B1 — ley de dilución de fase (explicación física)**: con `a_lat = a₀/T₀²` (aceleración de
    la celda de red, de `a₀` y `T₀` certificados) y `n = t_U/T₀` ticks en la edad del universo,
    `a_tr = a_lat / (2πn)`.
    El `2πn` es la **fase total acumulada** en un tiempo de Hubble (2π por tick, LC1).
    Es decir: `a_tr` = aceleración de la red **diluida por la fase acumulada**; el `1/(2π)` es la
    normalización angular por tick (la misma de `ω₀ = 2π/T₀`), no un parámetro libre. -/
theorem atr_phase_dilution (a0 T0 tU n : ℝ) (hT : T0 ≠ 0) (hn : n = tU / T0) :
    (a0 / T0) / (2 * Real.pi * tU) = (a0 / T0 ^ 2) / (2 * Real.pi * n) := by
  rw [hn]
  field_simp
end TIE.B1
