/-
TIE — F2 (cierre del gap V1.3): análisis y linealidad.
Protocolo de auditoría v1.0: cada teorema cita la etiqueta del ítem y declara su gap.

GAPS CONOCIDOS (auditoría 2026-10-31 → 2026-11-04): cada teorema declara su gap (G5) en el
docstring; la tabla canónica está en README.md y el detalle por ítem en REGISTRO_CIERRE_GAP.csv.
-/
import Mathlib
namespace TIE
open Filter
/-- **TT6 (límite continuo — cociente incremental)**: la derivada es exactamente el límite del
    cociente incremental `(f(x+t) − f(x))/t` cuando `t → 0` con `t ≠ 0`. Es el núcleo de TT6(ii)
    (diferencias finitas → derivada).
    Gap declarado (Gap 5): se apoya en la caracterización de Mathlib
    (`hasDerivAt_iff_tendsto_slope_zero`); NO se formalizan la convergencia de las sumas de
    Riemann (TT6(i)) ni la ecuación de onda discreta (TT6(iii)). -/
theorem tt6_difference_quotient (f : ℝ → ℝ) (f' x : ℝ) :
    HasDerivAt f f' x ↔
      Tendsto (fun t : ℝ => (f (x + t) - f x) / t) (nhdsWithin 0 {0}ᶜ) (nhds f') := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
/-- **TM4 (superposición lineal)**: si dos campos resuelven una ecuación lineal homogénea, su suma
    también (punto 1 de TM4: `Ψ_total = Ψ₁ + Ψ₂`).
    Gap declarado (Gap 5): formaliza sólo la linealidad; la excepción gravitatoria (no lineal, TMG)
    y los puntos 2–4 de TM4 no se modelan. -/
theorem tm4_superposition {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    (L : E →+ F) (φ1 φ2 : E) (h1 : L φ1 = 0) (h2 : L φ2 = 0) : L (φ1 + φ2) = 0 := by
  rw [map_add, h1, h2, add_zero]

/-- **TA2 (tensor de energía-momento de partícula puntual)**: el tensor `T_ij = K·v_i·v_j` es
    simétrico. Formaliza la estructura `v_i v_j` del tensor del texto (con `v_i = h_ij ẋ^j`).
    Gap declarado (Gap 5): simetría algebraica del tensor; NO se formaliza la variación de la
    acción ni la distribución delta (fuente del campo). -/
noncomputable def Tpp (K : ℝ) (v : Fin 3 → ℝ) (i j : Fin 3) : ℝ := K * v i * v j
theorem ta2_stress_symmetry (K : ℝ) (v : Fin 3 → ℝ) :
    ∀ i j : Fin 3, Tpp K v i j = Tpp K v j i := by
  intro i j
  unfold Tpp
  ring

/-- **TA1 (límite no relativista — cota superior)**: para `0 ≤ x ≤ 1`,
    `√(1−x) ≤ 1 − x/2`. Es el paso que produce el Lagrangiano newtoniano `½mv² − mc²` desde el
    relativista a primer orden (el defecto es `≈ x²/8`).
    Gap declarado (Gap 5): cota analítica de la raíz; NO se formaliza la integral de acción ni la
    variación que reproduce TM1. -/
theorem ta1_sqrt_upper (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (1 - x) ≤ 1 - x / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith [sq_nonneg x]

/-- **TA1 (cota del Lagrangiano)**: con `m c² > 0`, el Lagrangiano relativista
    `−mc²√(1−x)` queda por debajo del newtoniano `−mc²(1 − x/2)` en `0 ≤ x ≤ 1`.
    Gap declarado (Gap 5): corolario algebraico de `ta1_sqrt_upper`. -/
theorem ta1_lagrangian_bound (m c x : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -(m * c^2 * (1 - x / 2)) ≤ -(m * c^2 * Real.sqrt (1 - x)) := by
  have hpos : 0 < m * c^2 := by positivity
  have h := ta1_sqrt_upper x hx0 hx1
  nlinarith [h, hpos]

/-- **TA1 (cota inferior de segundo orden)**: para `0 ≤ x ≤ 1`,
    `1 − x/2 − x²/2 ≤ √(1−x)`. Junto con `ta1_sqrt_upper` fija el error del desarrollo a `O(x²)`.
    Gap declarado (Gap 5): cota analítica. -/
theorem ta1_sqrt_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x / 2 - x^2 / 2 ≤ Real.sqrt (1 - x) := by
  have h1 : 0 ≤ 1 - x := by linarith
  have h2 : 0 ≤ 1 - x / 2 - x^2 / 2 := by nlinarith [sq_nonneg (x - 1), sq_nonneg x]
  have h3 : (1 - x / 2 - x^2 / 2)^2 ≤ 1 - x := by nlinarith [sq_nonneg x, sq_nonneg (x^2)]
  nlinarith [Real.sq_sqrt h1, Real.sqrt_nonneg (1 - x), h1, h2, h3]

/-- **TM1 (movimiento general — núcleo libre)**: para una partícula libre, la posición es afín en
    el tiempo, `x(t) = x₀ + v·t`, y su derivada es la velocidad constante `v`.
    Gap declarado (Gap 5): núcleo cinemático del caso libre; NO se modela el vector de estado de
    7 componentes ni el acoplamiento a γ_ij, A^μ, ρ_I (eso queda en F4). -/
theorem tm1_free_motion (x0 v : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x0 + v * s) v t := by
  have h2 : HasDerivAt (fun s : ℝ => v * s) v t := by
    simpa using (hasDerivAt_id t).const_mul v
  simpa using h2.const_add x0

/-- **PT2 (independencia y separación absoluta)**: en la métrica bloque-diagonal
    `g = g_T ⊕ g_S` (con `g_T = a·dt²`, `g_S = b·dx²`) no hay término cruzado entre un vector
    temporal puro `(t,0)` y uno espacial puro `(0,x)`.
    Gap declarado (Gap 5): núcleo bilineal de la separación; la ontología de PT2 no se formaliza. -/
noncomputable def gBlock (a b : ℝ) (p q : ℝ × ℝ) : ℝ := a * p.1 * q.1 + b * p.2 * q.2
theorem pt2_no_cross_term (a b t x : ℝ) : gBlock a b (t, 0) (0, x) = 0 := by
  unfold gBlock
  ring

/-- **TG4 (identidad de Bianchi ⇒ conservación)**: si el tensor de Einstein satisface `G = κ·T`
    y su divergencia se anula, la de `T` también (linealidad de la divergencia, `κ ≠ 0`).
    Gap declarado (Gap 5): álgebra lineal de la conservación; la identidad de Bianchi y la
    ecuación de campo se toman como hipótesis. -/
theorem tg4_conservation {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (D : E →ₗ[ℝ] F) (G T : E) (κ : ℝ) (hκ : κ ≠ 0)
    (hG : G = κ • T) (h : D G = 0) : D T = 0 := by
  rw [hG, map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hκ

/-- **TA8 (tensor de energía-momento total)**: si cada componente se conserva, la suma también
    (linealidad de la divergencia).
    Gap declarado (Gap 5): aditividad de la conservación; las expresiones explícitas de cada
    `T` no se modelan. -/
theorem ta8_total_conserved {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (D : E →ₗ[ℝ] F) (T1 T2 : E)
    (h1 : D T1 = 0) (h2 : D T2 = 0) : D (T1 + T2) = 0 := by
  rw [map_add, h1, h2, add_zero]
end TIE
