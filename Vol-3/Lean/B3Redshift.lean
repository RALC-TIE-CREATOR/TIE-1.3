/-
B3 — TC2: derivación de PC4 desde la estructura de ticks y ley z = e^{H0 d/c} - 1.
Carpeta: tie-review/teoria-abierta/B3-TC2-redshift/
Resultado: perdida fraccional 1/n = H0*T0 por tick => dE/dl = -(H0/c)E (PC4) exacto;
ley exponencial equivalente a ln(1+z) = H0 d/c.
-/
import Mathlib
namespace TIE.B3
/-- **B3 — pérdida por tick**: si cada tick multiplica la energía por `(1 − 1/n)`,
tras `N` ticks `E_N = E_0 (1 − 1/n)^N`. -/
theorem tick_loss (E : ℕ → ℝ) (n : ℝ) (h : ∀ k, E (k+1) = E k * (1 - 1/n)) :
    ∀ N, E N = E 0 * (1 - 1/n)^N := by
  intro N
  induction N with
  | zero => simp
  | succ k ih => rw [h k, ih]; ring
/-- **B3 — identidad de PC4**: con `H₀ = 1/(nT₀)`, la pérdida `E/n` por tick de longitud `cT₀`
es exactamente `(H₀/c)·E`. -/
theorem rate_identity (E n T0 c H0 : ℝ) (hn : n ≠ 0) (hT : T0 ≠ 0) (hc : c ≠ 0)
    (hH : H0 = 1 / (n * T0)) :
    (E * (1/n)) / (c * T0) = E * H0 / c := by
  rw [hH]
  field_simp
/-- **B3 — ley exponencial**: `z = e^x − 1` es equivalente a `ln(1+z) = x`. -/
theorem z_exp_iff_log (x z : ℝ) (hz : 0 < 1 + z) :
    z = Real.exp x - 1 ↔ Real.log (1 + z) = x := by
  constructor
  · intro h
    rw [h]
    have h1 : (1:ℝ) + (Real.exp x - 1) = Real.exp x := by ring
    rw [h1, Real.log_exp]
  · intro h
    have h1 : 1 + z = Real.exp x := by
      rw [← h, Real.exp_log hz]
    linarith
end TIE.B3
