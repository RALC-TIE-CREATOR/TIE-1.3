/-
TIE — Primitivos y derivados (estructura minima de la teoria)  [V1.2, Capa 11]

Los **primitivos** de la TIE son los cuantos minimos de tiempo, espacio y masa:
    T0  -- cuanto minimo de tiempo   (PT5)
    a0  -- cuanto minimo de espacio  (PE1)
    m0  -- masa fundamental          (PM0; calibrada a escala Planck)
Todo lo demas es **definicion o teorema**. En particular:
    c   = a0/T0
    hbar = m0 c^2 T0 = m0 a0^2/T0    (derivado; E-57)
    lP = a0/sqrt(2pi);  tP = T0/sqrt(2pi)
    omega0 = 2pi/T0
    E0  = pi*hbar/T0 = h/(2T0)
    G   = a0^3/(2 pi T0^2 m0)
Identidad central: lP^2 = hbar G / c^3 = a0^2/(2 pi).
-/
import Mathlib
namespace TieFormal
/-- Primitivos de la TIE: cuantos minimos de tiempo (`T0`), espacio (`a0`) y masa (`m0`). -/
structure PrimitivosTIE where
  T0 : ℝ
  a0 : ℝ
  m0 : ℝ
  T0_pos : 0 < T0
  a0_pos : 0 < a0
  m0_pos : 0 < m0
namespace PrimitivosTIE
noncomputable section
variable (P : PrimitivosTIE)
/-- Velocidad de propagacion de fase (derivada): `c = a0/T0`. -/
def c : ℝ := P.a0 / P.T0
/-- Longitud de Planck (derivada): `lP = a0/sqrt(2pi)`. -/
def lP : ℝ := P.a0 / Real.sqrt (2 * Real.pi)
/-- Tiempo de Planck (derivado): `tP = T0/sqrt(2pi)`. -/
def tP : ℝ := P.T0 / Real.sqrt (2 * Real.pi)
/-- Frecuencia angular fundamental (derivada): `omega0 = 2pi/T0`. -/
def omega0 : ℝ := 2 * Real.pi / P.T0
/-- Accion fundamental (derivada; E-57): `hbar = m0 c^2 T0`. -/
def hbar : ℝ := P.m0 * P.c ^ 2 * P.T0
/-- Energia maxima del cuanto (derivada): `E0 = pi*hbar/T0`. -/
def E0 : ℝ := Real.pi * P.hbar / P.T0
/-- Constante de gravitacion emergente (derivada): `G = a0^3/(2 pi T0^2 m0)`. -/
def G : ℝ := P.a0 ^ 3 / (2 * Real.pi * P.T0 ^ 2 * P.m0)
lemma two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
lemma sqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr two_pi_pos
lemma sqrt2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt sqrt2pi_pos
lemma sq_sqrt2pi : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt two_pi_pos.le
lemma T0_ne : P.T0 ≠ 0 := ne_of_gt P.T0_pos
lemma a0_ne : P.a0 ≠ 0 := ne_of_gt P.a0_pos
lemma m0_ne : P.m0 ≠ 0 := ne_of_gt P.m0_pos
lemma c_ne : P.c ≠ 0 := by rw [c]; exact div_ne_zero P.a0_ne P.T0_ne
lemma hbar_ne : P.hbar ≠ 0 := by rw [hbar]; exact mul_ne_zero (mul_ne_zero P.m0_ne (pow_ne_zero 2 P.c_ne)) P.T0_ne
theorem a0_eq_sqrt_lP : P.a0 = Real.sqrt (2 * Real.pi) * P.lP := by rw [lP]; field_simp [sqrt2pi_ne]
theorem T0_eq_sqrt_tP : P.T0 = Real.sqrt (2 * Real.pi) * P.tP := by rw [tP]; field_simp [sqrt2pi_ne]
theorem G_eq_c : P.G = P.c ^ 3 * P.a0 ^ 2 / (2 * Real.pi * P.hbar) := by
  have ha : P.a0 = P.c * P.T0 := by rw [c]; field_simp [P.T0_ne]
  rw [G, hbar, ha]; field_simp [P.T0_ne, P.c_ne, P.m0_ne]; try ring
theorem lP_sq_a0 : P.lP ^ 2 = P.a0 ^ 2 / (2 * Real.pi) := by rw [lP, div_pow, sq_sqrt2pi]
theorem lP_sq : P.lP ^ 2 = P.hbar * P.G / P.c ^ 3 := by rw [lP_sq_a0, G_eq_c]; field_simp [P.hbar_ne, P.c_ne]
theorem c_mul_tP : P.c * P.tP = P.lP := by rw [c, tP, lP]; field_simp [P.T0_ne, sqrt2pi_ne]
theorem lP_div_tP : P.lP / P.tP = P.c := by rw [c, tP, lP]; field_simp [P.T0_ne, sqrt2pi_ne]
/-- `hbar = m0 a0 c` (equivalente a E-57 con `a0 = c T0`). -/
theorem hbar_eq_m0 : P.hbar = P.m0 * P.a0 * P.c := by
  rw [hbar, c]; field_simp [P.T0_ne]; try ring
theorem E0_eq : P.E0 = 2 * Real.pi * P.hbar / (2 * P.T0) := by rw [E0]; field_simp [P.T0_ne]
end
end PrimitivosTIE
end TieFormal
