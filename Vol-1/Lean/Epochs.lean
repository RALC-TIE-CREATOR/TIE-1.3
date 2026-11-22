/-
TIE — Dos edades (D-2(vi)): t_mat = F * t_U, t0 = (1 - F) * t_U.
-/
import Mathlib

namespace TIE

/-- **D-2(vi)**: la edad pre-material `t0 = (1-F)*tU` es positiva si `F < 1` y `tU > 0`. -/
theorem t0_positive (F tU : ℝ) (hF : F < 1) (htU : 0 < tU) : 0 < (1 - F) * tU := by
  have : 0 < 1 - F := by linarith
  exact mul_pos this htU

/-- **D-2(vi)**: la descomposición de la edad, que vale **por definición** de las dos edades
    (`t_mat := F*tU`, `t0 := (1-F)*tU`): `F*tU + (1-F)*tU = tU`. No es un resultado físico. -/
theorem ages_sum_of_defs (F tU : ℝ) : F * tU + (1 - F) * tU = tU := by ring

end TIE
