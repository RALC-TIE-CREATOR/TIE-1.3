/-
TIE — Backlog real (cierre del gap V1.3): núcleos de los ítems restantes.

GAPS CONOCIDOS (auditoría 2026-10-31 → 2026-11-04): cada teorema declara su gap (G5) en el
docstring; la tabla canónica está en README.md y el detalle por ítem en REGISTRO_CIERRE_GAP.csv.
-/
import Mathlib
import TieFormal.CampoRhoI
namespace TIE
/-- **TT13 (no-go de rotación del contenedor)**: si el potencial gravitomagnético `A_g` es nulo,
    la precesión de Lense-Thirring se anula: `Ω_LT(c, 0) = 0`.
    Gap declarado (Gap 5): núcleo algebraico del no-go (sin `g0i` no hay arrastre); la afirmación
    de que el vacío estático tiene `g0i = 0` no se formaliza aquí. -/
theorem tt13_no_frame_dragging (c : ℝ) : OmegaLT c 0 = 0 := by
  unfold OmegaLT smul3
  ext <;> simp

/-- **TG3 (ecuaciones de campo exactas — traza)**: de `G = κ·T` se sigue `tr G = κ·tr T`
    (linealidad de la traza). Es el núcleo lineal de las ecuaciones exactas.
    Gap declarado (Gap 5): no se modela la forma explícita `G_μν = R_μν − ½R g_μν`. -/
theorem tg3_trace_relation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (tr : E →ₗ[ℝ] ℝ) (G T : E) (κ : ℝ) (h : G = κ • T) : tr G = κ * tr T := by
  rw [h, map_smul]
  rfl

/-- **Álgebra PPN (NO es TG2)**: la diferencia entre `1 - 2u + 2βu²` y `(1-u)²` es `(2β-1)u²`.
    Revisión semántica 2026-11-04: el enunciado de TG2 NO usa β (usa `N = 1 + Φ/c²` y
    `h_ij = (1 - 2Φ/c²)δ_ij`); esta identidad se conserva como álgebra PPN estándar. -/
theorem tg2_ppn_deviation (u β : ℝ) :
    (1 - 2 * u + 2 * β * u^2) - (1 - u)^2 = (2 * β - 1) * u^2 := by
  ring

/-- **TG8 (potencia radiada por un sistema binario)**: la fórmula `P = K/a⁵` escala como `a⁻⁵`
    (`P(ka) = P(a)/k⁵`).
    Gap declarado (Gap 5): escalado de la fórmula; el coeficiente `32G⁴/5c⁵·(m₁m₂)²(m₁+m₂)`
    no se deriva. -/
theorem tg8_power_scaling (K a k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) :
    K / (k * a)^5 = K / a^5 / k^5 := by
  field_simp

/-- **Identidad del fluido perfecto (NO es TA6)**: traza `-ρ + 3p` con `u·u = -1` y `tr g = 4`.
    Revisión semántica 2026-11-04: el `T` de TA6 es `(ħ²/2m)(∇ψ*∇ψ + c.c.) + h L_φ`, que NO es
    fluido perfecto; esta identidad se conserva como álgebra estándar. -/
theorem ta6_trace_perfect_fluid (ρ p uu : ℝ) (hu : uu = -1) :
    (ρ + p) * uu + p * 4 = -ρ + 3 * p := by
  rw [hu]
  ring

/-- **TG1 (expansión perturbativa del campo gravitacional)**: identidad exacta de inversión
    `1/(a+h) = 1/a − h/a² + h²/(a²(a+h))`: el término lineal de la perturbación es `−h/a²`.
    Gap declarado (Gap 5): álgebra de la linealización; la expansión tensorial completa
    (`g = g⁰ + h`) no se modela. -/
theorem tg1_inverse_expansion (a h : ℝ) (ha : a ≠ 0) (hah : a + h ≠ 0) :
    1 / (a + h) = 1 / a - h / a^2 + h^2 / (a^2 * (a + h)) := by
  field_simp
  ring

/-- **TG9 (tensor efectivo de energía-momento gravitacional)**: el tensor efectivo es CUADRÁTICO
    en las primeras derivadas del campo: `K·(λq)² = λ²·(K·q²)`.
    Gap declarado (Gap 5): homogeneidad cuadrática; la expresión explícita en Christoffels no se
    modela. -/
theorem tg9_quadratic (K q lam : ℝ) : K * (lam * q)^2 = lam^2 * (K * q^2) := by
  ring

/-- **TT20 (simetría de la sombra en el límite estático)**: la frontera de la sombra es un disco,
    y un disco es invariante bajo rotaciones: `(R_θ p)² = p²` para toda `θ`.
    Gap declarado (Gap 5): núcleo geométrico (invariancia rotacional); NO se derivan las
    geodésicas nulas que fijan el radio de la sombra. -/
theorem tt20_shadow_rotational_symmetry (θ x y : ℝ) :
    (Real.cos θ * x - Real.sin θ * y)^2 + (Real.sin θ * x + Real.cos θ * y)^2 = x^2 + y^2 := by
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- **TG2 (1PN — núcleo real del texto)**: con `N = 1 + Φ/c²`, la componente temporal de la
    métrica es `g₀₀ = −N²c² = −(c² + 2Φ + Φ²/c²)` (el término de primer orden es `−2Φ`).
    Revisión semántica 2026-11-04: este es el enunciado de TG2 (el texto NO usa β).
    Gap declarado (Gap 5): identidad algebraica de `N`; `γ̃₀₀ = −4Φ/c²` y la ecuación de Poisson
    no se formalizan. -/
theorem tg2_lapse_metric (Φ c : ℝ) (hc : c ≠ 0) :
    -((1 + Φ / c^2)^2 * c^2) = -(c^2 + 2 * Φ + Φ^2 / c^2) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp
  ring

/-- **TA6 (traza del T del campo de fase — enunciado real)**: para
    `T^{ij} = K(∂^iψ∂^jψ + ∂^jψ∂^iψ) + h^{ij}L` con `h` Euclídea en 3D (`h_{ij}h^{ij} = 3`),
    la traza es `T = 2K|∇ψ|² + 3L`, escrito en componentes `(g₀,g₁,g₂)`.
    Revisión semántica 2026-11-04: este es el `T` de TA6 (NO fluido perfecto).
    Gap declarado (Gap 5): se toma `h = δ` (caso 1PN del texto); `K = ħ²/2m` no se sustituye. -/
theorem ta6_trace_phase_field (K L g0 g1 g2 : ℝ) :
    (2 * K * g0 ^ 2 + L) + (2 * K * g1 ^ 2 + L) + (2 * K * g2 ^ 2 + L)
      = 2 * K * (g0 ^ 2 + g1 ^ 2 + g2 ^ 2) + 3 * L := by
  ring

/-- **TT10 (límite newtoniano de la métrica)**: con `r_s = 2GM/c²` y `Φ = −GM/r`, se cumple
    `1 − r_s/r = 1 + 2Φ/c²`: la componente temporal de Schwarzschild reproduce el potencial
    newtoniano a primer orden.
    Gap declarado (Gap 5): identidad algebraica del límite; la equivalencia PN completa no. -/
theorem tt10_newtonian_limit (G M c r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) :
    1 - (2 * G * M / c^2) / r = 1 + 2 * (-G * M / r) / c^2 := by
  field_simp
  ring

/-- **TT13 (contenedor vs métrica efectiva)**: `Ω_LT = 0` componente a componente si y sólo si
    `A_g = 0`. El contenedor (sin `g0i`) no precesa; la métrica efectiva (con `g0i ≠ 0`) sí.
    Gap declarado (Gap 5): equivalencia algebraica; la afirmación ontológica sobre el contenedor
    no se formaliza. -/
theorem tt13_lt_zero_iff (c g1 g2 g3 : ℝ) (hc : c ≠ 0) :
    (c^2 * g1 = 0 ∧ c^2 * g2 = 0 ∧ c^2 * g3 = 0) ↔ (g1 = 0 ∧ g2 = 0 ∧ g3 = 0) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(mul_eq_zero.mp h1).resolve_left hc2,
           (mul_eq_zero.mp h2).resolve_left hc2,
           (mul_eq_zero.mp h3).resolve_left hc2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨by ring, by ring, by ring⟩

/-- **TT20 (potencial en L² ⇒ simetría especular)**: si el potencial efectivo depende sólo de
    `L²`, es invariante bajo `L → −L` (la reflexión `α → −α` del texto).
    Gap declarado (Gap 5): núcleo de la simetría; la derivación del potencial desde la métrica no. -/
theorem tt20_potential_reflection (f : ℝ → ℝ) (L : ℝ) : f (L^2) = f ((-L)^2) := by
  rw [neg_sq]
end TIE

