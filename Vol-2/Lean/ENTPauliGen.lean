/-
TIE — Ticket T02 (Entrelazamiento): G1 — exponencial general-n por conjugación explícita.
`U(n·σ)U⁻¹ = σ₃` (columnas: autovectores ±1) ⇒ `exp(iθ·n·σ) = cosθ·1 + i·senθ·(n·σ)`.
-/
import Mathlib
import TieFormal.ENTPauli
namespace TIE.ENT
/-- `exp(iθσ₃) = cosθ·1 + i·senθ·σ₃` (forma trigonométrica del caso eje). -/
theorem exp_theta_s3_cos_sin (θ : ℝ) :
    NormedSpace.exp (((θ : ℂ) * Complex.I) • s3) =
      ((Real.cos θ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * (Real.sin θ : ℂ)) • s3 := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    simpa using Complex.exp_ofReal_mul_I θ
  have h2 : Complex.exp (-((θ : ℂ) * Complex.I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -((θ : ℂ) * Complex.I) = (((-θ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [exp_theta_s3_diag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.add_apply, Matrix.smul_apply, s3, h1, h2] <;> ring
/-- Matriz de conjugación: columnas = autovectores ±1 de `n·σ`. -/
def conjU (n1 n2 n3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(n1 : ℂ) - Complex.I * (n2 : ℂ), (n1 : ℂ) - Complex.I * (n2 : ℂ);
     (1 : ℂ) - (n3 : ℂ), -((1 : ℂ) + (n3 : ℂ))]
/-- `U` conjuga `n·σ` a `σ₃`: `(n·σ)·U = U·σ₃`. -/
theorem conjU_spec (n1 n2 n3 : ℝ) (h : n1^2 + n2^2 + n3^2 = 1) :
    nSig n1 n2 n3 * conjU n1 n2 n3 = conjU n1 n2 n3 * s3 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;>
      simp [nSig, conjU, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
      ring_nf <;> nlinarith [h]
/-- Determinante de `U`. -/
theorem conjU_det (n1 n2 n3 : ℝ) :
    (conjU n1 n2 n3).det = -2 * ((n1 : ℂ) - Complex.I * (n2 : ℂ)) := by
  rw [Matrix.det_fin_two]
  simp [conjU]
  ring
/-- **G1**: `exp(iθ(n·σ)) = cosθ·1 + i·senθ·(n·σ)` para `n` unitaria arbitraria. -/
theorem exp_theta_gen (n1 n2 n3 : ℝ) (h : n1^2 + n2^2 + n3^2 = 1) (θ : ℝ) :
    NormedSpace.exp (((θ : ℂ) * Complex.I) • nSig n1 n2 n3) =
      ((Real.cos θ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (Complex.I * (Real.sin θ : ℂ)) • nSig n1 n2 n3 := by
  by_cases hc : ((n1 : ℂ) - Complex.I * (n2 : ℂ)) = 0
  · have h1 : n1 = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have h2 : n2 = 0 := by
      have := congrArg Complex.im hc
      simpa using this
    subst h1
    subst h2
    have h3 : n3 = 1 ∨ n3 = -1 := by
      have hz : n3 ^ 2 = 1 := by nlinarith [h]
      exact sq_eq_one_iff.mp hz
    rcases h3 with rfl | rfl
    · have hA : nSig 0 0 1 = s3 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [nSig, s1, s2, s3]
      rw [hA, exp_theta_s3_cos_sin]
    · have hA : nSig 0 0 (-1) = -s3 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [nSig, s1, s2, s3]
      rw [hA]
      rw [show ((θ : ℂ) * Complex.I) • (-s3) = ((((-θ : ℝ)) : ℂ) * Complex.I) • s3 by
        rw [smul_neg, ← neg_smul]
        congr 1
        push_cast
        ring]
      rw [exp_theta_s3_cos_sin]
      rw [show ((Real.cos (-θ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * (Real.sin (-θ) : ℂ)) • s3
          = ((Real.cos θ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.I * (Real.sin θ : ℂ)) • (-s3) by
        rw [Real.cos_neg, Real.sin_neg, smul_neg, ← neg_smul]
        congr 1
        congr 1
        push_cast
        ring]
  · have hUdet : IsUnit (conjU n1 n2 n3).det := by
      rw [conjU_det]
      exact isUnit_iff_ne_zero.mpr (by
        intro hzero
        apply hc
        rcases mul_eq_zero.mp hzero with h' | h'
        · norm_num at h'
        · exact h')
    have hU : IsUnit (conjU n1 n2 n3) := (Matrix.isUnit_iff_isUnit_det _).mpr hUdet
    have hA : nSig n1 n2 n3 = conjU n1 n2 n3 * s3 * (conjU n1 n2 n3)⁻¹ := by
      have hspec := conjU_spec n1 n2 n3 h
      have hright : nSig n1 n2 n3 * conjU n1 n2 n3 * (conjU n1 n2 n3)⁻¹ = nSig n1 n2 n3 := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv (conjU n1 n2 n3) hUdet, Matrix.mul_one]
      rw [← hright, hspec, Matrix.mul_assoc]
    rw [hA]
    rw [show ((θ : ℂ) * Complex.I) • (conjU n1 n2 n3 * s3 * (conjU n1 n2 n3)⁻¹)
        = conjU n1 n2 n3 * (((θ : ℂ) * Complex.I) • s3) * (conjU n1 n2 n3)⁻¹ by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]]
    rw [Matrix.exp_conj _ _ hU, exp_theta_s3_cos_sin]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv (conjU n1 n2 n3) hUdet, ← hA]
/-- **G1(b)**: `exp(iπ(n·σ)) = −I₂` para `n` unitaria arbitraria. -/
theorem exp_pi_gen (n1 n2 n3 : ℝ) (h : n1^2 + n2^2 + n3^2 = 1) :
    NormedSpace.exp (((Real.pi : ℂ) * Complex.I) • nSig n1 n2 n3) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [exp_theta_gen n1 n2 n3 h Real.pi]
  simp [Real.cos_pi, Real.sin_pi]
/-- **G1(b)**: `exp(i2π(n·σ)) = +I₂` para `n` unitaria arbitraria. -/
theorem exp_two_pi_gen (n1 n2 n3 : ℝ) (h : n1^2 + n2^2 + n3^2 = 1) :
    NormedSpace.exp (((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) • nSig n1 n2 n3) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [exp_theta_gen n1 n2 n3 h (2 * Real.pi)]
  simp [Real.cos_two_pi, Real.sin_two_pi]
end TIE.ENT
