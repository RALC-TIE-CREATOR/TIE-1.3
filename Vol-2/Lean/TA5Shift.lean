/-
TIE — E-24: TA5 con el corrimiento cuantico. El factor 1/N del termino temporal
se cancela contra la medida sh ≡ sqrt(h); la EOM es i*hbar*d_t(psi) = N*H*psi.
-/
import Mathlib

namespace TIE

/-- **E-24**: cancelación lapso/medida: `(N * (1/N)) * sh * X = sh * X` si `N != 0`,
    con `sh` el factor de medida (`sh ≡ sqrt h`). -/
theorem lapse_measure_cancellation (N sh X : ℝ) (hN : N ≠ 0) :
    N * (1 / N) * sh * X = sh * X := by
  field_simp

/-- **E-24**: la EOM acoplada `K*dpsi = N*H*psi` con `K = i*hbar != 0` da
    `dpsi = (N*H*psi)/K`: el lapso entra como factor global (corrimiento cuantico). -/
theorem quantum_shift_form (K N H psi dpsi : ℝ) (hK : K ≠ 0)
    (h : K * dpsi = N * H * psi) : dpsi = (N * H * psi) / K := by
  rw [eq_div_iff hK, mul_comm dpsi K]
  exact h

end TIE
