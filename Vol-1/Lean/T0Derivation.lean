/-
TIE — Derivación del espaciamiento fundamental a = √(2π) ℓ_P y de T₀ = √(2π) t_P
(Aporte del autor, ver DERIVACION_a_T0.md.)

Núcleo algebraico de las dos vías (hipótesis físicas declaradas, NO demostradas aquí):

  Vía 2 (rigidez de la red + G emergente):
    (H1) G = c³ a² / (2π ℏ)          [de μ = ℏ c / a⁴]
    (H2) ℓ_P² = ℏ G / c³             [definición de la longitud de Planck]
    ⟹ a² = 2π ℓ_P²   ⟹   a = √(2π) ℓ_P.

  Vía 1 (densidad de estados):
    (H1') a³ = (2π)^{3/2} ℓ_P³
    ⟹ a = √(2π) ℓ_P.

  Corolario: con t_P = ℓ_P/c y T₀ = a/c,  T₀ = √(2π) t_P.
-/
import Mathlib

namespace TieFormal

open Real

/-- **Vía 2 (núcleo algebraico).** De `G = c³a²/(2πℏ)` y `ℓ_P² = ℏG/c³` se sigue `a² = 2π ℓ_P²`. -/
theorem via2_algebra (c a hbar G lP : ℝ) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (hG : G = c ^ 3 * a ^ 2 / (2 * Real.pi * hbar))
    (hlP : lP ^ 2 = hbar * G / c ^ 3) :
    a ^ 2 = 2 * Real.pi * lP ^ 2 := by
  rw [hlP, hG]
  field_simp

/-- **Vía 2 (raíz).** Con `a, ℓ_P ≥ 0`, `a = √(2π) ℓ_P`. -/
theorem via2_sqrt (c a hbar G lP : ℝ) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (ha : 0 ≤ a) (hlp : 0 ≤ lP)
    (hG : G = c ^ 3 * a ^ 2 / (2 * Real.pi * hbar))
    (hlP : lP ^ 2 = hbar * G / c ^ 3) :
    a = sqrt (2 * Real.pi) * lP := by
  have h : a ^ 2 = 2 * Real.pi * lP ^ 2 := via2_algebra c a hbar G lP hc hh hG hlP
  have hsqrt : a = sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
  rw [hsqrt, h]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.sqrt_sq hlp]

/-- **Vía 1 (núcleo algebraico).** De `a³ = (2π)^{3/2} ℓ_P³` (escrito `2π·√(2π) ℓ_P³`)
se sigue `a = √(2π) ℓ_P` (inyectividad del cubo). -/
theorem via1 (a lP : ℝ)
    (h : a ^ 3 = 2 * Real.pi * sqrt (2 * Real.pi) * lP ^ 3) :
    a = sqrt (2 * Real.pi) * lP := by
  have hsq2 : (sqrt (2 * Real.pi)) ^ 3 = sqrt (2 * Real.pi) * (2 * Real.pi) := by
    have : (sqrt (2 * Real.pi)) ^ 3
        = sqrt (2 * Real.pi) * (sqrt (2 * Real.pi)) ^ 2 := by ring
    rw [this, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hcube : (sqrt (2 * Real.pi) * lP) ^ 3
      = 2 * Real.pi * sqrt (2 * Real.pi) * lP ^ 3 := by
    rw [mul_pow, hsq2]; ring
  rw [← hcube] at h
  exact (show Odd (3 : ℕ) from ⟨1, by norm_num⟩).strictMono_pow.injective h

/-- **Corolario T₀.** Con `t_P = ℓ_P/c`, `T₀ = a/c` y `a = √(2π) ℓ_P`, se tiene `T₀ = √(2π) t_P`. -/
theorem T0_eq (c a lP tP T0 : ℝ) (hc : c ≠ 0)
    (htP : tP = lP / c) (hT0 : T0 = a / c)
    (ha : a = sqrt (2 * Real.pi) * lP) :
    T0 = sqrt (2 * Real.pi) * tP := by
  rw [hT0, ha, htP]
  field_simp

end TieFormal
