/-
TIE PDI — Principio de Distorsión Instrumental (cap. 1, §1.4)

Formalización del núcleo matemático de PDI. La función de distorsión
instrumental es

    Φ ≡ dτ/dt = 2·ω_R/ω₀ ,

donde ω_R es la frecuencia efectiva de un reloj material y ω₀ la frecuencia
de referencia (la frecuencia de Nyquist del reloj ideal es ω₀/2).

Se certifican (sin postulados físicos, solo matemática):
  · PDI–cota:  0 ≤ Φ ≤ 1  ↔  0 ≤ ω_R ≤ ω₀/2   (ω₀ > 0);
  · PDI–saturación:  Φ = 1  ↔  ω_R = ω₀/2  (reposo absoluto sin campo);
  · el puente LT1:  E = ℏ·ω_R ≤ ℏ·ω₀/2 = E₀;
  · la forma relativista Φ(v) = √(1 − v²/c²) cumple 0 ≤ Φ ≤ 1.

Las interpretaciones físicas ("reposo absoluto", "ausencia de campo") entran
como parámetros/hipótesis del modelo; lo que aquí se prueba es su contenido
matemático (desigualdades y equivalencias).
-/
import Mathlib

namespace TIE

/-- La función de distorsión instrumental Φ = 2·ω_R/ω₀ (PDI). -/
noncomputable def Phi (ωR ω0 : ℝ) : ℝ := 2 * ωR / ω0

/-- PDI, cota inferior: Φ ≥ 0 ↔ ω_R ≥ 0 (para ω₀ > 0). -/
theorem Phi_nonneg (ωR ω0 : ℝ) (h0 : 0 < ω0) : 0 ≤ Phi ωR ω0 ↔ 0 ≤ ωR := by
  unfold Phi
  rw [div_nonneg_iff]
  constructor
  · intro h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · linarith
    · exact absurd h2 (not_le_of_gt h0)
  · intro h
    exact Or.inl ⟨by linarith, le_of_lt h0⟩

/-- PDI, cota superior: Φ ≤ 1 ↔ ω_R ≤ ω₀/2 (para ω₀ > 0). -/
theorem Phi_le_one (ωR ω0 : ℝ) (h0 : 0 < ω0) : Phi ωR ω0 ≤ 1 ↔ ωR ≤ ω0 / 2 := by
  unfold Phi
  rw [div_le_iff₀ h0]
  constructor <;> intro h <;> linarith

/-- **PDI (cota universal)**: 0 ≤ Φ ≤ 1 ↔ 0 ≤ ω_R ≤ ω₀/2. -/
theorem Phi_bounds (ωR ω0 : ℝ) (h0 : 0 < ω0) :
    0 ≤ Phi ωR ω0 ∧ Phi ωR ω0 ≤ 1 ↔ 0 ≤ ωR ∧ ωR ≤ ω0 / 2 := by
  rw [Phi_nonneg ωR ω0 h0, Phi_le_one ωR ω0 h0]

/-- **PDI (saturación)**: Φ = 1 ↔ ω_R = ω₀/2 (reposo absoluto sin campo). -/
theorem Phi_eq_one_iff (ωR ω0 : ℝ) (h0 : 0 < ω0) : Phi ωR ω0 = 1 ↔ ωR = ω0 / 2 := by
  unfold Phi
  rw [div_eq_iff (ne_of_gt h0)]
  constructor <;> intro h <;> linarith

/-- Puente LT1: la energía del reloj está acotada por E₀ = ℏ·ω₀/2. -/
theorem energy_bound (h_bar ωR ω0 : ℝ) (hℏ : 0 < h_bar) (hR : ωR ≤ ω0 / 2) :
    h_bar * ωR ≤ h_bar * (ω0 / 2) :=
  mul_le_mul_of_nonneg_left hR (le_of_lt hℏ)

/-- La forma relativista Φ(v) = √(1 − v²/c²) (c > 0), **en el dominio físico `v² ≤ c²`**:
    0 ≤ Φ ≤ 1 y `Φ² = 1 − v²/c²` (fuera del dominio la identidad falla: el `sqrt` se satura). -/
theorem Phi_lorentz_bounds (v c : ℝ) (hc : 0 < c) (hv : v^2 ≤ c^2) :
    0 ≤ Real.sqrt (1 - v^2 / c^2) ∧ Real.sqrt (1 - v^2 / c^2) ≤ 1 ∧
      (Real.sqrt (1 - v^2 / c^2))^2 = 1 - v^2 / c^2 := by
  have hnn : (0:ℝ) ≤ 1 - v^2 / c^2 := by
    have hc2 : (0:ℝ) < c^2 := by positivity
    have hle : v^2 / c^2 ≤ 1 := by
      rw [div_le_one hc2]
      exact hv
    linarith
  refine ⟨Real.sqrt_nonneg _, ?_, Real.sq_sqrt hnn⟩
  rw [Real.sqrt_le_one]
  have h0 : (0:ℝ) ≤ v^2 / c^2 := by positivity
  linarith

/-- La forma relativista es monótona decreciente en |v| en [0, c]. -/
theorem Phi_lorentz_antitone (c : ℝ) (hc : 0 < c) :
    AntitoneOn (fun v => Real.sqrt (1 - v^2 / c^2)) (Set.Icc 0 c) := by
  intro a ha b hb hab
  have hca : 0 ≤ a := ha.1
  have hbc : b ≤ c := hb.2
  have hsq : a^2 ≤ b^2 := by nlinarith [hab, hca, hb.1]
  apply Real.sqrt_le_sqrt
  have hb2 : 0 < c^2 := by positivity
  rw [sub_le_sub_iff_left, div_le_div_iff_of_pos_right hb2]
  exact hsq

end TIE
