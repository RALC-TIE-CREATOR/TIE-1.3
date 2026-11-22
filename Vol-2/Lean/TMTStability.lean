/-
TIE — Linea 5 (TMT-E1), modulo 3 (ESTABILIDAD, entregables A2 + C1a).
(1) A2: el minimo por ciclo es la fase UNIFORME, E_gamma = n J (1 - cos(2 pi omega/n)).
(2) C1a: la conservacion del winding NO se certifica aqui (requiere pi_1(S^1), no modelado);
    el contenido real de conservacion esta en TMTWinding.windTerm_eq_of_band.
    V(phi) solo fija el offset U(1), no crea la estabilidad (hallazgo numerico del equipo TMT).
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **A2**: energia del minimo (fase uniforme) con winding `omega` en un ciclo de `n` aristas. -/
noncomputable def Ecycle (n J omega : ℝ) : ℝ := n * J * (1 - Real.cos (2 * Real.pi * omega / n))
/-- **A2 (caso omega=1, n=4)**: `Delta phi = pi/2`, luego `E = 4 J (1 - cos(pi/2)) = 4 J`. -/
theorem Ecycle_w1_n4 (J : ℝ) : Ecycle 4 J 1 = 4 * J := by
  unfold Ecycle
  have h : 2 * Real.pi * 1 / 4 = Real.pi / 2 := by ring
  rw [h, Real.cos_pi_div_two]; ring
/-- **A2**: el sector trivial (omega=0) da `E=0` (fase uniforme), como debe. -/
theorem Ecycle_w0 (n J : ℝ) : Ecycle n J 0 = 0 := by unfold Ecycle; simp
/-- **A2 (chequeo de definiciones)**: `C` = numero de minimos por sector topologico:
    dona 3, rosca 5, figura 8 1 (valores de las constantes definidas en TMTConfig). -/
theorem C_min_counts : (Craw, Cros, Cfig) = (3, 5, 1) := rfl
end TIE.TMT
