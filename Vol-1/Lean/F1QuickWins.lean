/-
TIE — F1 (cierre del gap Lean V1.3): quick wins.
Protocolo de auditoría v1.0: cada teorema cita la etiqueta del ítem y declara su gap.

GAPS CONOCIDOS (auditoría 2026-10-31 → 2026-11-04): cada teorema declara su gap (G5) en el
docstring; la tabla canónica está en README.md y el detalle por ítem en REGISTRO_CIERRE_GAP.csv.
-/
import Mathlib
namespace TIE
/-- **PT4 (núcleo algebraico)**: homogeneidad del retículo de ticks = invariancia de las
    diferencias bajo traslación: `(n+k) - (m+k) = n - m`.
    Gap declarado (Gap 5): se formaliza el núcleo algebraico de la homogeneidad
    (invariancia traslacional del retículo), no la ontología del postulado. -/
theorem pt4_homogeneity (n m k : ℤ) : (n + k) - (m + k) = n - m := by ring
/-- **PT4 (sin origen privilegiado)**: toda traslación del retículo es biyectiva. -/
theorem pt4_translation_bijective (k : ℤ) : Function.Bijective (fun n : ℤ => n + k) := by
  constructor
  · intro a b h
    simpa using h
  · intro b
    exact ⟨b - k, by ring⟩
/-- **CO2 (producto de primer orden)**: la expansión de la función de distorsión multiplicativa
    `(1-a)(1-b)` tiene término cruzado exacto `a*b` (el O(v² r_s / c² r) del texto).
    Gap declarado (Gap 5): identidad algebraica; no deriva la fórmula de TT11. -/
theorem co2_first_order_product (a b : ℝ) : (1 - a) * (1 - b) = 1 - a - b + a * b := by ring
/-- **CO2 (aritmética del corrimiento GPS)**: los términos del texto suman el neto declarado
    (+45.7 gravitacional, −7.2 cinemático → +38.5) y el valor calculado (+38.52) dista menos
    de 0.2 microsegundos/día del operacional (+38.4).
    Gap declarado (Gap 5): chequeo aritmético de las cifras del texto, no una derivación. -/
theorem co2_gps_arithmetic :
    ((45.7 : ℝ) + (-7.2) = 38.5) ∧ |(38.52 : ℝ) - 38.4| < 0.2 := by
  constructor <;> norm_num
/-- **CO3 (redshift gravitacional)**: para `0 < r_s < r₁ < r₂`, el cociente de distorsiones
    `Φ(r₂)/Φ(r₁)` es mayor que 1, luego `z = Φ₂/Φ₁ − 1 > 0` (corrimiento al rojo).
    Gap declarado (Gap 5): núcleo algebraico-analítico (monotonía de √(1−r_s/r));
    no se deriva la fórmula desde la acción. -/
theorem co3_redshift_positive (rs r1 r2 : ℝ) (hrs : 0 < rs) (h1 : rs < r1) (h12 : r1 < r2) :
    1 < Real.sqrt (1 - rs / r2) / Real.sqrt (1 - rs / r1) := by
  have hr1 : 0 < r1 := lt_trans hrs h1
  have hr2 : 0 < r2 := lt_trans hr1 h12
  have hA : 0 < 1 - rs / r1 := by
    have h : rs / r1 < 1 := (div_lt_one hr1).2 h1
    linarith
  have hB : 0 < 1 - rs / r2 := by
    have h : rs / r2 < 1 := (div_lt_one hr2).2 (by linarith)
    linarith
  have hlt : 1 - rs / r1 < 1 - rs / r2 := by
    have h : rs / r2 < rs / r1 := div_lt_div_of_pos_left hrs hr1 h12
    linarith
  have hden : 0 < Real.sqrt (1 - rs / r1) := Real.sqrt_pos.2 hA
  have hnum : Real.sqrt (1 - rs / r1) < Real.sqrt (1 - rs / r2) :=
    Real.sqrt_lt_sqrt (le_of_lt hA) hlt
  rw [one_lt_div hden]
  exact hnum

/-- **LT2 (dispersión covariante)**: la relación `ω²/f − c²h^{ij}k_i k_j = ω_C²` se invierte
    algebraicamente como `ω² = f·(c²h^{ij}k_i k_j + ω_C²)`.
    Gap declarado (Gap 5): inversión algebraica de la relación del texto (no se deriva del WKB). -/
theorem lt2_dispersion_solve (w2 f c2S wC2 : ℝ) (hf : f ≠ 0)
    (h : w2 / f - c2S = wC2) : w2 = f * (c2S + wC2) := by
  field_simp at h ⊢
  linarith

/-- **TT10 (métrica de Schwarzschild)**: identidad de los factores de la métrica TIE de vacío
    `g_tt·g_rr = −c²`, con `g_tt = −(1−r_s/r)c²` y `g_rr = 1/(1−r_s/r)`.
    Gap declarado (Gap 5): identidad algebraica de la métrica; no se deriva de EC1*/EC2*. -/
theorem tt10_schwarzschild_identity (rs r c : ℝ) (h : 1 - rs / r ≠ 0) :
    (-(1 - rs / r) * c^2) * (1 / (1 - rs / r)) = -c^2 := by
  field_simp

/-- **TT21 (sombra de Sgr A*)**: consistencia numérica del texto: `D_TIE = 52.3 μas` frente a
    EHT 2022 `51.8 ± 2.3 μas` → diferencia `0.5 μas < 2.3` y dentro de `0.25σ`.
    Gap declarado (Gap 5): chequeo aritmético de las cifras publicadas. -/
theorem tt21_sgrA_consistency :
    |(52.3 : ℝ) - 51.8| < 2.3 ∧ |(52.3 : ℝ) - 51.8| / 2.3 < 0.25 := by
  constructor <;> norm_num

/-- **CO5 (Gravity Probe B)**: las diferencias de la tabla del texto están dentro de `1.1σ`
    (geodético: |−6620.9 + 6601.8|/18.3 ≈ 1.04) y de `0.3σ` (Lense–Thirring: 2.0/7.2 ≈ 0.28).
    Gap declarado (Gap 5): chequeo aritmético de la tabla comparativa. -/
theorem co5_gpb_sigma :
    |(-6620.9 : ℝ) - (-6601.8)| / 18.3 < 1.1 ∧ |(-39.2 : ℝ) - (-37.2)| / 7.2 < 0.3 := by
  constructor <;> norm_num

/-- **CO6 (Sagnac)**: diferencia de fase `Δφ = (4ω_fotón/c²)·ω·A`; su linealidad en el área.
    Gap declarado (Gap 5): definición del texto + linealidad; no se deriva de ρ_I. -/
noncomputable def sagnacPhase (wphoton c omega A : ℝ) : ℝ := 4 * wphoton / c^2 * omega * A

theorem co6_sagnac_additive (wphoton c omega A1 A2 : ℝ) (hc : c ≠ 0) :
    sagnacPhase wphoton c omega (A1 + A2)
      = sagnacPhase wphoton c omega A1 + sagnacPhase wphoton c omega A2 := by
  unfold sagnacPhase
  ring

/-- **CO1 (Hafele–Keating)**: la función de distorsión de TT11 factoriza en una sola raíz:
    `√(1−r_s/r)·√(1−v²/c²) = √((1−r_s/r)(1−v²/c²))` para `r > r_s`, `v² ≤ c²`.
    Gap declarado (Gap 5): identidad usada en la integral del texto; la integración numérica
    de las trayectorias no se reproduce. -/
theorem co1_distortion_factorization (rs r v c : ℝ) (hr : 0 < r) (hrs : rs ≤ r)
    (hv : v^2 ≤ c^2) (hc : c ≠ 0) :
    Real.sqrt (1 - rs / r) * Real.sqrt (1 - v^2 / c^2)
      = Real.sqrt ((1 - rs / r) * (1 - v^2 / c^2)) := by
  have hx : 0 ≤ 1 - rs / r := by
    have h1 : rs / r ≤ 1 := (div_le_one hr).2 hrs
    linarith
  rw [← Real.sqrt_mul hx]

/-- **TE4 (ausencia de singularidades accesibles)**: para `0 < r_s < r`, la distorsión
    `Φ(r) = √(1−r_s/r)` es estrictamente positiva y menor que 1: no hay divergencia ni cero
    en el dominio exterior.
    Gap declarado (Gap 5): núcleo analítico; la afirmación ontológica sobre 𝒮 no se formaliza. -/
theorem te4_phi_positive (rs r : ℝ) (hrs : 0 < rs) (h : rs < r) :
    0 < Real.sqrt (1 - rs / r) ∧ Real.sqrt (1 - rs / r) < 1 := by
  have hr : 0 < r := lt_trans hrs h
  have hpos : 0 < rs / r := div_pos hrs hr
  have hx : 0 < 1 - rs / r := by
    have h1 : rs / r < 1 := by
      rw [div_lt_one hr]; exact h
    linarith
  refine ⟨Real.sqrt_pos.2 hx, ?_⟩
  have h1 : Real.sqrt (1 - rs / r) < Real.sqrt 1 := by
    apply Real.sqrt_lt_sqrt (le_of_lt hx)
    linarith
  simpa using h1

/-- **TT18 (dominio efectivo no vacío)**: existen radios que son a la vez exteriores al horizonte
    y mayores que el espaciado de red: `∃ r, r_s < r ∧ a₀ ≤ r`.
    Gap declarado (Gap 5): existencia del dominio; no se formaliza la dinámica discreta para `r < a₀`. -/
theorem tt18_domain_nonempty (rs a0 : ℝ) : ∃ r : ℝ, rs < r ∧ a0 ≤ r := by
  refine ⟨max rs a0 + 1, ?_, ?_⟩
  · have := le_max_left rs a0; linarith
  · have := le_max_right rs a0; linarith

/-- **TT2 (función de distorsión cinemática)**: `Φ(v) = √(1−v²/c²)` factoriza como
    `√((1−v/c)(1+v/c))` en el dominio físico `|v| ≤ c`.
    Gap declarado (Gap 5): identidad algebraica de la función de distorsión; la derivación
    desde PT10 no se formaliza aquí (ver `PDI.Phi_lorentz_bounds`). -/
theorem tt2_phi_factorization (v c : ℝ) (hc : 0 < c) (hv : v^2 ≤ c^2) :
    Real.sqrt (1 - v^2 / c^2) = Real.sqrt ((1 - v / c) * (1 + v / c)) := by
  have hc2 : (0:ℝ) < c^2 := by positivity
  have h1 : 1 - v^2 / c^2 = (1 - v / c) * (1 + v / c) := by
    field_simp
    ring
  rw [h1]

/-- **LC1 (acoplamiento de fases)**: si la frecuencia propia coincide con la de referencia
    (`ω = ω₀`), la fase interna en el tick `n` es exactamente `2πn`.
    Gap declarado (Gap 5): identidad algebraica del caso bloqueado; el caso general es la fórmula
    del texto (`φ = 2πn·ω/ω₀`) evaluada. -/
theorem lc1_phase_locked (n : ℕ) (w w0 : ℝ) (hw : w0 ≠ 0) (h : w = w0) :
    2 * Real.pi * n * (w / w0) = 2 * Real.pi * n := by
  subst h
  field_simp

/-- **LM1 (momento angular fundamental)**: la relación `m·r = ħ/c = cte` implica la dualidad
    `m₂/m₁ = r₁/r₂` entre dos defectos.
    Gap declarado (Gap 5): álgebra de la relación; `L = ħ` se toma como definición del cuanto. -/
theorem lm1_mass_radius_duality (m1 m2 r1 r2 : ℝ) (hm : m1 ≠ 0) (hr : r1 ≠ 0)
    (h : m1 * r1 = m2 * r2) : m2 / m1 = r1 / r2 := by
  have hr2 : r2 ≠ 0 := by
    intro h0
    have hz : m1 * r1 = 0 := by rw [h, h0, mul_zero]
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact hm h1
    · exact hr h1
  field_simp
  nlinarith [h]
/-- **TM2 (conservación intrínseca)**: si una propiedad intrínseca `m(t)` es constante, su
    derivada temporal es nula en todo instante (`dm/dt = 0`).
    Gap declarado (Gap 5): formaliza el núcleo «constante ⇒ derivada nula»; la conservación
    física se postula, no se deriva. -/
theorem tm2_conservation (m : ℝ → ℝ) (c : ℝ) (h : ∀ t, m t = c) (t : ℝ) :
    HasDerivAt m 0 t := by
  rw [show m = fun _ => c from funext h]
  exact hasDerivAt_const t c
end TIE
