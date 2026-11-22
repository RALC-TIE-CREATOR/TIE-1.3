/-
TIE — Teoría del Tiempo (Cap. 1), paso T3: estructura temporal
Simultaneidad (TT3), déficit instrumental (TT4) y causalidad (TT5).

Solo matemática (teoría de órdenes y aritmética); la física entra como
definición de los objetos. Una vez cerrada la teoría del tiempo se pasa a la
del espacio (cap. 2, TE).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TT3 (simultaneidad absoluta)**: la simultaneidad es la igualdad de tick;
es una relación de equivalencia sobre los eventos `T⁰ × 𝒮` (independiente de observador). -/
theorem tt3_simultaneity {X : Type*} :
    Equivalence (fun (a b : ℕ × X) => a.1 = b.1) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- **TT4 (déficit no negativo)**: con `Φ_i ≤ 1`, el déficit instrumental
acumulado `δ = Σ (1 − Φ_i) Δt_i` es no negativo. -/
theorem tt4_deficit_nonneg {ι : Type*} (s : Finset ι) (Φ dt : ι → ℝ)
    (hdt : ∀ i ∈ s, 0 ≤ dt i) (hΦ : ∀ i ∈ s, Φ i ≤ 1) :
    0 ≤ ∑ i ∈ s, (1 - Φ i) * dt i := by
  apply Finset.sum_nonneg
  intro i hi
  have := hΦ i hi
  have := hdt i hi
  nlinarith

/-- **TT4 (el reloj no adelanta al tiempo absoluto)**: `Σ Φ_i Δt_i ≤ Σ Δt_i`. -/
theorem tt4_clock_no_exceed {ι : Type*} (s : Finset ι) (Φ dt : ι → ℝ)
    (hdt : ∀ i ∈ s, 0 ≤ dt i) (hΦ : ∀ i ∈ s, Φ i ≤ 1) :
    ∑ i ∈ s, Φ i * dt i ≤ ∑ i ∈ s, dt i := by
  apply Finset.sum_le_sum
  intro i hi
  have := hΦ i hi
  have := hdt i hi
  nlinarith

/-- **TT5 (relación causal)**: en `T¹ × 𝒮` (tick continuo × posición 1D),
`a ≺_c b` sii `n_a < n_b` y `|x_b − x_a| ≤ c·(n_b − n_a)·T₀`. -/
def CausalRel (c T0 : ℝ) (a b : ℝ × ℝ) : Prop :=
  a.1 < b.1 ∧ |b.2 - a.2| ≤ c * (b.1 - a.1) * T0

/-- **TT5 (transitividad)**: la relación causal es transitiva. -/
theorem tt5_transitive (c T0 : ℝ) (a b d : ℝ × ℝ)
    (hab : CausalRel c T0 a b) (hbd : CausalRel c T0 b d) :
    CausalRel c T0 a d := by
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨h3, h4⟩ := hbd
  refine ⟨lt_trans h1 h3, ?_⟩
  have ht : d.1 - a.1 = (b.1 - a.1) + (d.1 - b.1) := by ring
  calc |d.2 - a.2| ≤ |d.2 - b.2| + |b.2 - a.2| := abs_sub_le _ _ _
    _ ≤ c * (d.1 - b.1) * T0 + c * (b.1 - a.1) * T0 := add_le_add h4 h2
    _ = c * (d.1 - a.1) * T0 := by rw [ht]; ring

/-- **TT5 (el orden causal está contenido en el temporal)**: `≺_c ⊆ ≺_t`. -/
theorem tt5_causal_subset_temporal (c T0 : ℝ) :
    ∀ a b, CausalRel c T0 a b → a.1 < b.1 := fun _ _ h => h.1

end TIE
