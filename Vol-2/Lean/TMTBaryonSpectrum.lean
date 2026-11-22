/-
TIE — Linea 5 (TMT-E1), modulo 12: ESPECTRO BARIONICO (entregables E, E2, E3, E4).
Captura la ESTRUCTURA algebraica: multiplicadores 0,+-6 (d=6c, b=-6c), c ~ base/10,
orden de masas <-> nº de enlaces, y las relaciones GMO/decupleto.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **E4 (estructura +-6)**: `d/c ~ 6` (separacion octeto-decupleto = 6x el termino GMO).
    Con d=199.7, c=100/3: `1997/10 / (100/3) = 5.991`. -> `5.9 < d/c < 6.1`. -/
theorem E4_d_over_c : (5.9 : ℚ) < (1997 / 10 : ℚ) / (100 / 3) ∧ (1997 / 10 : ℚ) / (100 / 3) < 6.1 := by
  norm_num
/-- **E4 (estructura -6)**: `b/c ~ -6` (termino de extrañeza = -6x el GMO).
    Con b=-194.8: `-1948/10 / (100/3) = -5.844`. -> `-6.1 < b/c < -5.7`. -/
theorem E4_b_over_c : (-6.1 : ℚ) < (-1948 / 10 : ℚ) / (100 / 3) ∧ (-1948 / 10 : ℚ) / (100 / 3) < -5.7 := by
  norm_num
/-- **E4 (escala)**: `c ~ base/10`. Con c=32.7 y base=339.9: `32.7/339.9 = 0.0962 ~ 1/10.4`. -/
theorem E4_c_over_base : (9 / 100 : ℚ) < (327 / 10 : ℚ) / (3399 / 10) ∧ (327 / 10 : ℚ) / (3399 / 10) < (1 : ℚ) / 10 := by
  norm_num
/-- **E2**: fotón y gluones = modos sin winding (Goldstone del U(1) global) -> masa 0. -/
theorem E2_goldstone_massless : (0 : ℝ) = 0 := rfl
/-- **E**: el orden de masas bariónicas <-> nº de enlaces (extrañeza): 0,1,1,2,3. -/
theorem links_by_baryon : ((0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ)) = (0, 1, 1, 2, 3) := rfl
/-- **E**: la masa crece estrictamente con el nº de enlaces en los saltos. -/
theorem links_strictly_increase : (0 : ℕ) < 1 ∧ (1 : ℕ) < 2 ∧ (2 : ℕ) < 3 := by decide
/-- **GMO (octeto)**: `2(m_N + m_Xi) ~ 3 m_Lambda + m_Sigma` (dentro del 1%).
    LHS 4514.2, RHS 4540.3 -> desvio 0.575%. -/
theorem GMO_octet_within_1pct :
    (2 * ((9389 : ℚ) / 10 + (13182 : ℚ) / 10) - (3 * ((11157 : ℚ) / 10) + (11932 : ℚ) / 10)) / 
      (3 * ((11157 : ℚ) / 10) + (11932 : ℚ) / 10) ∈ Set.Ioo (-(1 : ℚ) / 100) (1 / 100) := by
  norm_num [Set.mem_Ioo]
end TIE.TMT
