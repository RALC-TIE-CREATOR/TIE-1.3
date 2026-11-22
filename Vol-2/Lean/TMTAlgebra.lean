/-
TIE — Topología Toroidal (Cap. 4, TMT): paso TMT1 (BARRIDO_TMT_LEAN.md)

Identidades algebraicas del capítulo:
  (a) **Kerr–Newman**: a = J/(Mc) con J = ℏ/2 da a = ℏ/(2mc); el texto (V1.3) fija R_mayor = 1,28×(ℏ/2mc) (§7), no exactamente a;
  (b) **Poynting (lazo plano)**: S_z = R·U/c con U = mc² y R = ℏ/(mc) da S_z = ℏ (§8, Ap. A).

Nota (A04-01): NO se formaliza la cadena LTT1-Rev ↔ tabla 2.1, que el texto
presenta como internamente inconsistente (los r tabulados dan k·R≈0.58–0.64, no 1/2).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **Kerr–Newman (§7)**: con `J = ℏ/2`, `a = J/(Mc) = ℏ/(2mc) = R_mayor`. -/
theorem kn_radius (hbar m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    (hbar / 2) / (m * c) = hbar / (2 * m * c) := by
  field_simp

/-- **Poynting, lazo plano (§8)**: `S_z = R·U/c` con `U = m·c²` y `R = ℏ/(m·c)`
    da `S_z = ℏ`. -/
theorem poynting_loop (hbar m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    hbar / (m * c) * (m * c^2) / c = hbar := by
  field_simp

end TIE
