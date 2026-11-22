/-
TIE — D-2(ii): teorema de no-fuga. La rama compuesta 1+z = (1+z_D)(1+z_P) con
componente disipativa de primer orden (z_P > 0) da un deficit 1+z_D < 1+z,
excluido por la escala (1+z) observada.

GAPS CONOCIDOS (auditoria 2026-10-30, bloque C):
  · composite_deficit certifica UN PASO (déficit positivo), no el argumento de no-fuga completo:
    la exclusión por los datos NO se formaliza (Gap 4 declarado; el nombre del módulo es más amplio).
-/
import Mathlib

namespace TIE

/-- **D-2(ii)**: con `z_D >= 0` y `z_P > 0`, la rama compuesta da `1+z_D < (1+z_D)(1+z_P)`:
    el deficit fraccionario es positivo (luego excluido por los datos). -/
theorem composite_deficit (zD zP : ℝ) (hzD : 0 ≤ zD) (hzP : 0 < zP) :
    1 + zD < (1 + zD) * (1 + zP) := by
  have h1 : 0 < 1 + zD := by linarith
  have h2 : 0 < (1 + zD) * zP := mul_pos h1 hzP
  nlinarith [h2]

end TIE
