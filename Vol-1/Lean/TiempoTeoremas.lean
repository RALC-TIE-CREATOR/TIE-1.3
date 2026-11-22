/-
TIE — Teoría del Tiempo (Cap. 1): primera tanda de teoremas en Lean
Fase «Tiempo», pasos T1/T2/T4/T5 del barrido (BARRIDO_TT_LEAN.md).

Contenido certificado (sin postulados físicos, solo matemática):
  · LT1 — de la dispersión ω² = c²k² + ω_C² y las definiciones E=ℏω, p=ℏk,
    ω_C = m c²/ℏ, se sigue la relación relativista E² = p²c² + m²c⁴;
  · TT9 — Φ_TIE(r) = √(1 − r_s/r) está en [0,1] (horizonte en r = r_s);
  · TT11 — Φ(v,r) = √(1 − r_s/r)·√(1 − v²/c²) está en [0,1];
  · TT12 — espectro de modos colectivos E = m·E₀/N ∈ (0, E₀] para 1 ≤ m ≤ N;
  · PT14 — el prefactor del sector cinético de la acción cuadrática:
    (c⁴/16πG)·(1/4c²) = c²/64πG.

Nota (A01a-F23): la derivación «acción PT14 → ecuaciones EC1*/EC2*» está rota
en el libro; aquí NO se formaliza. Solo el álgebra exacta de la acción.
-/
import Mathlib
import TieFormal.PDI

noncomputable section

namespace TIE

/-- **LT1**: la relación de dispersión relativista. De ω² = c²k² + ω_C² con
ω_C = m c²/ℏ (y ℏ ≠ 0), se sigue E² = p²c² + m²c⁴ con E = ℏω, p = ℏk. -/
theorem lt1_dispersion (ω k c m hbar : ℝ) (hℏ : hbar ≠ 0)
    (h : ω^2 = c^2 * k^2 + (m * c^2 / hbar)^2) :
    (hbar * ω)^2 = (hbar * k)^2 * c^2 + m^2 * c^4 := by
  calc (hbar * ω)^2 = hbar^2 * ω^2 := by ring
    _ = hbar^2 * (c^2 * k^2 + (m * c^2 / hbar)^2) := by rw [h]
    _ = (hbar * k)^2 * c^2 + m^2 * c^4 := by field_simp

/-- **TT9**: Φ_TIE(r) = √(1 − r_s/r) cumple 0 ≤ Φ ≤ 1 para 0 < r y r_s ≤ r. -/
theorem tt9_Phi_bounds (rs r : ℝ) (hr0 : 0 < r) (hrs : 0 ≤ rs) (hr : rs ≤ r) :
    0 ≤ Real.sqrt (1 - rs / r) ∧ Real.sqrt (1 - rs / r) ≤ 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  rw [Real.sqrt_le_one]
  have : 0 ≤ rs / r := div_nonneg hrs (le_of_lt hr0)
  linarith

/-- **TT11**: Φ(v,r) = √(1 − r_s/r)·√(1 − v²/c²) cumple 0 ≤ Φ ≤ 1 (dominio físico `v² ≤ c²`). -/
theorem tt11_Phi_bounds (rs r v c : ℝ) (hr0 : 0 < r) (hrs : 0 ≤ rs) (hr : rs ≤ r)
    (hc : 0 < c) (hv : v^2 ≤ c^2) :
    0 ≤ Real.sqrt (1 - rs / r) * Real.sqrt (1 - v^2 / c^2) ∧
      Real.sqrt (1 - rs / r) * Real.sqrt (1 - v^2 / c^2) ≤ 1 := by
  obtain ⟨hs1, hs2⟩ := tt9_Phi_bounds rs r hr0 hrs hr
  obtain ⟨hv1, hv2, -⟩ := Phi_lorentz_bounds v c hc hv
  refine ⟨mul_nonneg hs1 hv1, ?_⟩
  have h := mul_le_mul hs2 hv2 hv1 (by norm_num : (0:ℝ) ≤ 1)
  simpa using h

/-- **TT12**: la energía del modo colectivo E = m·E₀/N con 1 ≤ m ≤ N está en (0, E₀]. -/
theorem tt12_spectrum (m N : ℕ) (E0 : ℝ) (hN : 0 < N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hE0 : 0 < E0) : 0 < (m : ℝ) * E0 / N ∧ (m : ℝ) * E0 / N ≤ E0 := by
  have hN' : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  refine ⟨div_pos (mul_pos hm' hE0) hN', ?_⟩
  rw [div_le_iff₀ hN']
  nlinarith [hmN', hE0]

/-- **PT14** (sector cinético de la acción cuadrática): (c⁴/16πG)·(1/4c²) = c²/64πG
    (con `Real.pi`, no una variable libre). -/
theorem pt14_kinetic_prefactor (c G : ℝ) (hc : c ≠ 0) (hG : G ≠ 0) :
    c^4 / (16 * Real.pi * G) * (1 / (4 * c^2)) = c^2 / (64 * Real.pi * G) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **TT22** (esqueleto algebraico): la condición de invarianza conforme
    −8 + 4α₁ = 0 fija α₁ = 2 (la derivación física completa queda documentada
    con los caveats A01a-F01/F02). -/
theorem tt22_alpha1 (α1 : ℝ) (h : -8 + 4 * α1 = 0) : α1 = 2 := by linarith

end TIE
