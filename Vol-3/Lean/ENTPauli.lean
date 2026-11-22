/-
TIE — Ticket ENT T01 (Entrelazamiento): P1 núcleo algebraico spin-½.
Pauli: (n·σ)² = I para n unitaria. (b)/(c): caso eje σ₃ certificado (exp_theta_s3_diag, exp_pi_s3); general-n (T02/G1) en curso.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.ENT
open Matrix
/-- σ₁. -/
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- σ₂. -/
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- σ₃. -/
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- `n·σ = n₁σ₁ + n₂σ₂ + n₃σ₃`. -/
def nSig (n1 n2 n3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (n1 : ℂ) • s1 + (n2 : ℂ) • s2 + (n3 : ℂ) • s3
/-- **P1(a)**: `(n·σ)² = I₂` para `n` unitaria. -/
theorem pauli_sq (n1 n2 n3 : ℝ) (h : n1^2 + n2^2 + n3^2 = 1) :
    nSig n1 n2 n3 * nSig n1 n2 n3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nSig, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.ext_iff, Complex.I_mul_I] <;>
    constructor <;> norm_num <;> nlinarith [h]
/-- **P1(b), caso eje**: `exp(iθ σ₃)` en forma diagonal (autovalores `e^{±iθ}`). -/
theorem exp_theta_s3_diag (θ : ℝ) :
    NormedSpace.exp (((θ : ℂ) * Complex.I) • s3) =
      diagonal (fun i : Fin 2 => if i = 0 then Complex.exp ((θ : ℂ) * Complex.I)
                                 else Complex.exp (-((θ : ℂ) * Complex.I))) := by
  have hdiag : ((θ : ℂ) * Complex.I) • s3 =
      diagonal (fun i : Fin 2 => if i = 0 then ((θ : ℂ) * Complex.I)
                                 else -((θ : ℂ) * Complex.I)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s3, Matrix.diagonal] <;> norm_num
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]
/-- **P1(c), caso eje**: `exp(iπ σ₃) = −I₂`. -/
theorem exp_pi_s3 :
    NormedSpace.exp ((Real.pi * Complex.I) • s3) = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have h2 : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, h1]; norm_num
  rw [exp_theta_s3_diag Real.pi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.neg_apply, Matrix.one_apply, h1, h2, ← Complex.exp_eq_exp_ℂ]
end TIE.ENT
