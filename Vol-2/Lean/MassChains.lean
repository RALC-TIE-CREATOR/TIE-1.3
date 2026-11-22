/-
TIE M4 — Cadenas de masa (TMT)

Resultados certificados (aritmética racional exacta sobre ℚ):
  · PD-T4: m₄ = ℏc / a_QCD  ⇒  2406 < m₄ < 2407 MeV  (valor 2406.41…);
  · PD-T4: R_τ = ℏc / m_τ   ⇒  R_τ > a_QCD  (0.111 > 0.082 fm);
  · la reformulación del arco k·R_M = s/(2π(2+r²)) como identidad algebraica
    exacta (recuperación de s), con el valor numérico de π certificado por
    cotas de intervalo en la Fase B (M2). La tabla de la familia (p,q) y las
    integrales de arco quedan como datos verificados numéricamente (Fase E).

Constantes declaradas: ℏc = 197.326 MeV·fm, a_QCD = 0.082 fm, m_τ = 1776.86 MeV.
-/
import Mathlib

namespace TIE

/-- ℏc en MeV·fm (valor declarado). -/
def hbarC : ℚ := 197326 / 1000

/-- El parámetro de red a_QCD en fm (valor declarado). -/
def aQCD : ℚ := 82 / 1000

/-- PD-T4: la masa del cuarto nivel, m₄ = ℏc / a_QCD. -/
def m4 : ℚ := hbarC / aQCD

/-- m₄ en forma reducida: 197326/82. -/
theorem m4_eq : m4 = 197326 / 82 := by unfold m4 hbarC aQCD; norm_num

/-- PD-T4: cotas certificadas de la masa del cuarto nivel (2406–2407 MeV). -/
theorem m4_bounds : 2406 < m4 ∧ m4 < 2407 := by
  unfold m4 hbarC aQCD; norm_num

/-- La masa del leptón τ en MeV (valor declarado). -/
def mTau : ℚ := 177686 / 100

/-- PD-T4: R_τ = ℏc / m_τ (en fm). -/
def Rtau : ℚ := hbarC / mTau

/-- PD-T4: R_τ supera el parámetro de red a_QCD (R_τ > 0.082 fm). -/
theorem Rtau_gt_aQCD : aQCD < Rtau := by
  unfold Rtau aQCD hbarC mTau; norm_num

/-- El dato de la tabla: r₀ = 0.50487… -/
def r0 : ℚ := 50487 / 100000

theorem r0_pos : 0 < r0 := by unfold r0; norm_num

/-- La reformulación del arco: k·R_M = s/(2π(2+r²)). -/
def kRM (s r p : ℚ) : ℚ := s / (2 * p * (2 + r^2))

/-- La reformulación recupera s: (k·R_M)·2π(2+r²) = s (identidad algebraica exacta). -/
theorem kRM_recover (s r p : ℚ) (hp : p ≠ 0) (hr : 2 + r^2 ≠ 0) :
            kRM s r p * (2 * p * (2 + r^2)) = s := by
  unfold kRM
  field_simp
  try ring

end TIE
