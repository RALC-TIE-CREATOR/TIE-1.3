/-
TIE — D-1: el canal rotacional (g_{0i}, restriccion de momento de PT14) y su
descripcion material rho_I dan la MISMA precesion (dualidad, lectura (a)).
B_g = 2 c^2 grad(rho_I);  Omega_LT = +c^2 grad(rho_I) = +1/2 B_g.
-/
import TieFormal.CampoRhoI

namespace TIE

/-- **D-1 (dualidad)**: la precesion del canal metrico coincide con la descripcion
    material: `Omega_LT = +c^2 * grad(rho_I)` (por definicion, `g = grad rho_I`). -/
theorem rotational_channel_dual (c : ℝ) (g : V3) :
    OmegaLT c g = smul3 (c^2) g := rfl

/-- **D-1**: `Omega_LT = +1/2 B_g`. -/
theorem rotational_channel_half_Bg (c : ℝ) (g : V3) :
    OmegaLT c g = smul3 (1/2) (BgOf c g) := OmegaLT_eq_pos_half_Bg c g

end TIE
