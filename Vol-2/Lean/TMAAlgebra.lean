/-
TIE — Acción (Cap. 5, TMA): paso TMA1 (BARRIDO_TMA_LEAN.md)

Álgebra vectorial del acoplamiento materia–campo (TA4): la fuerza de Lorentz
  F = q(E + v×B),
y su propiedad física clave: **la fuerza magnética no realiza trabajo**.

Reutiliza dot3/cross3 (CampoRhoI). El resto del capítulo es construcción de
acciones/EDO (física); ver el barrido para los caveats A05-01..A05-10.
-/
import Mathlib
import TieFormal.CampoRhoI

noncomputable section

namespace TIE

/-- **TA4 (fuerza magnética sin trabajo)**: `v · (v × B) = 0`. -/
theorem magnetic_no_work (v B : ℝ × ℝ × ℝ) : dot3 v (cross3 v B) = 0 := by
  simp [dot3, cross3]; ring

/-- **TA4 (potencia de Lorentz)**: con `F = q(E + v×B)`, la potencia es solo la
    eléctrica: `v · F = q (v · E)`. -/
theorem lorentz_power (q : ℝ) (v E B : ℝ × ℝ × ℝ) :
    dot3 v (q • (E + cross3 v B)) = q * dot3 v E := by
  simp [dot3, cross3]; ring

end TIE
