/-
TIE M2 — Aritmética de α⁻¹ (identidades exactas; cotas numéricas documentadas)
Cap. 4 (TMT, V1.3) / cap. 9 (TMK): la serie radiativa de α⁻¹.
Verificación: Mathlib (ring/norm_num/nlinarith).

GAPS CONOCIDOS (auditoria 2026-10-29):
  · F2_value: F2 = 12 se certifica en Combinatorics.kink_antikink_distribution (12+12);
    aqui NO se duplica (evita dependencia circular); antes era la tautologia 12 = 12 (corregido).
  · lpha_decomposition es aritmetica (3*12=36, 2*12=24), no una derivacion combinatoria (Gap 5).
  · La serie radiativa es un ANSATZ del corpus; aqui solo se certifican sus cotas de intervalo.
-/
import Mathlib

namespace TIE

/-! ## El término de nivel árbol -/

/-- A = 12(3π + 2) = 36π + 24: identidad exacta (ring). -/
theorem alpha_inv_base : (12:ℝ) * (3*Real.pi + 2) = 36*Real.pi + 24 := by ring

/-- Forma con M: A = M(3π + 2) para M = 12. -/
theorem alpha_inv_base_M (M : ℝ) (hM : M = 12) : M * (3*Real.pi + 2) = 36*Real.pi + 24 := by
  subst hM; ring

/-- La raíz combinatoria de la factorización: 36 = 3·12 y 24 = 2·12
    (de Γ₂₁: E = 3M y |O| = 2M con M = 12; ver Graph21). -/
theorem alpha_decomposition : 3 * 12 = 36 ∧ 2 * 12 = 24 := ⟨rfl, rfl⟩

/-- A = M(3π+2) con los dos factores: la base geométrica (3π) y el conteo (2). -/
theorem alpha_factors : (12:ℝ)*(3*Real.pi) = 36*Real.pi := by ring

/-! ## Los coeficientes radiativos (F₁ = 17, F₂ = 12, F₃ = 72, F₄ = 96) -/

/-- F₁ = β₀ + β₁ = 1 + 16 = 17 (compilado en Graph21: beta1 = 16). -/
theorem F1_value : 1 + 16 = (17:ℕ) := rfl

/- **F₂ = 12**: se certifica en `Combinatorics.kink_antikink_distribution` (12 + 12 plaquetas);
   aquí no se duplica para no crear dependencia circular. (Antes era la tautología `12 = 12`.) -/

/-- F₃ = 72 = 24·3: pares de plaquetas que comparten arista (3 por plaqueta · 24). -/
theorem F3_value : 24 * 3 = (72:ℕ) := rfl

/-- F₄ = 96 = 24·4: la traza Tr(BᵀB) = 4 aristas por plaqueta × 24 plaquetas. -/
theorem F4_value : 24 * 4 = (96:ℕ) := rfl

/-! ## La serie radiativa -/

/-- La serie radiativa completa: A − F₁/2A + F₂/A² + F₃/A³ − F₄/A⁴, con A = 36π + 24. -/
noncomputable def serieRadiativa : ℝ :=
  (36*Real.pi + 24) - 17/(2*(36*Real.pi + 24)) + 12/(36*Real.pi + 24)^2
    + 72/(36*Real.pi + 24)^3 - 96/(36*Real.pi + 24)^4

/-- La identidad estructural de la serie (definición expandida). -/
theorem serie_forma : serieRadiativa =
    (36*Real.pi + 24) - 17/(2*(36*Real.pi + 24)) + 12/(36*Real.pi + 24)^2
    + 72/(36*Real.pi + 24)^3 - 96/(36*Real.pi + 24)^4 := rfl

/-- El término de corrección de 1 bucle, como fracción de A: F₁/(2A) = 17/(2A). -/
theorem correccion_1loop (A : ℝ) (hA : A = 36*Real.pi + 24) :
    17/(2*A) = 17/(2*(36*Real.pi + 24)) := by rw [hA]

/-! ## Cota numérica (estado: documentada; certificación en la iteración siguiente)

La cadena de cotas rigurosa — con π acotado por las constantes racionales de Mathlib
(`Real.pi_gt_d20`, `Real.pi_lt_d20`) y aritmética de intervalos sobre A = 36π + 24 —
requiere la táctica de intervalos; el esquema probado es:

  137.0973355292321 < A < 137.0973355292322
  ⇒  serieRadiativa ∈ (137.03599917, 137.03600432)  (cotas racionales por término)
  ⇒  |serieRadiativa − 137.0360019| < 1e-4

Estatus: los valores racionales intermedios están verificados en el acta numérica
(Python/auditoría); la transcripción del intervalo a Lean queda como paso de
certificación pendiente (ver PLAN_LEAN.md, Fase D). -/

/-- La consistencia de la meta numérica: 137.0360019 está dentro de la banda declarada
    para CODATA 137.035999177 ± 0.0001 (aritmética racional directa). -/
theorem cota_objetivo_consistente :
    |(137.0360019:ℝ) - 137.035999177| < 0.0001 := by norm_num

/-! ## Cota de intervalo CERTIFICADA (Fase B)

Estrategia: π acotado por Mathlib a 20 dígitos (`pi_gt_d20`/`pi_lt_d20`)
⟹ A = 36π + 24 ∈ (137.09733552, 137.09733553)
⟹ u = A⁻¹ ∈ (0.007294088, 0.007294089)
⟹ cada término de la serie acotado por aritmética racional
⟹ serieRadiativa ∈ (137.0360018775, 137.0360018966).

Verificación numérica independiente (Python): serieRadiativa = 137.0360019 ✓ -/

/-- **M2 — el intervalo riguroso de la serie**: `137.0360018 ≤ serieRadiativa < 137.036002`.
    (Con π acotado por Mathlib a 20 dígitos y aritmética racional por término.) -/
theorem serieRadiativa_acotada :
    137.03600185 ≤ serieRadiativa ∧ serieRadiativa < 137.036002 := by
  have hA1 : (137.09733552:ℝ) < 36 * Real.pi + 24 := by
    have := Real.pi_gt_d20; linarith
  have hA2 : 36 * Real.pi + 24 < 137.09733553 := by
    have := Real.pi_lt_d20; linarith
  have hApos : (0:ℝ) < 36 * Real.pi + 24 := lt_trans (by norm_num) hA1
  have hup : (0:ℝ) < (36*Real.pi + 24)⁻¹ := by positivity
  have hup2 : (0:ℝ) < (36*Real.pi + 24)⁻¹^2 := by positivity
  have hup3 : (0:ℝ) < (36*Real.pi + 24)⁻¹^3 := by positivity
  have hU1 : (0:ℝ) < 0.007294087 := by norm_num
  have hU1q : (0:ℝ) < 0.007294087^2 := by norm_num
  have hU1c : (0:ℝ) < 0.007294087^3 := by norm_num
  have hU2 : (0:ℝ) < 0.007294088 := by norm_num
  have hU2q : (0:ℝ) < 0.007294088^2 := by norm_num
  have hu1 : (0.007294087:ℝ) < (36*Real.pi + 24)⁻¹ := by
    rw [← one_div, lt_div_iff₀ hApos]
    have h1 : (0.007294087:ℝ) * (36*Real.pi + 24) < 0.007294087 * 137.09733553 :=
      mul_lt_mul_of_pos_left hA2 hU1
    have h2 : (0.007294087:ℝ) * 137.09733553 ≤ 1 := by norm_num
    linarith
  have hu2 : (36*Real.pi + 24)⁻¹ < 0.007294088 := by
    rw [← one_div, div_lt_iff₀ hApos]
    have h1 : (1:ℝ) < 0.007294088 * 137.09733552 := by norm_num
    have h2 : (0.007294088:ℝ) * 137.09733552 < 0.007294088 * (36*Real.pi + 24) :=
      mul_lt_mul_of_pos_left hA1 hU2
    linarith
  have hsq_ub : (36*Real.pi + 24)⁻¹^2 < (0.007294088:ℝ)^2 := by
    rw [pow_two, pow_two]
    have s1 : (36*Real.pi + 24)⁻¹ * (36*Real.pi + 24)⁻¹
        < 0.007294088 * (36*Real.pi + 24)⁻¹ := mul_lt_mul_of_pos_right hu2 hup
    have s2 : (0.007294088:ℝ) * (36*Real.pi + 24)⁻¹ < 0.007294088 * 0.007294088 :=
      mul_lt_mul_of_pos_left hu2 hU2
    exact lt_trans s1 s2
  have hsq_lb : (0.007294087:ℝ)^2 < (36*Real.pi + 24)⁻¹^2 := by
    rw [pow_two, pow_two]
    have s1 : (0.007294087:ℝ) * 0.007294087
        < 0.007294087 * (36*Real.pi + 24)⁻¹ := mul_lt_mul_of_pos_left hu1 hU1
    have s2 : (0.007294087:ℝ) * (36*Real.pi + 24)⁻¹
        < (36*Real.pi + 24)⁻¹ * (36*Real.pi + 24)⁻¹ := mul_lt_mul_of_pos_right hu1 hup
    exact lt_trans s1 s2
  have hcu3_ub : (36*Real.pi + 24)⁻¹^3 < (0.007294088:ℝ)^3 := by
    nlinarith [hsq_ub, hu2, hup, hU2]
  have hcu3_lb : (0.007294087:ℝ)^3 < (36*Real.pi + 24)⁻¹^3 := by
    nlinarith [hsq_lb, hu1, hup, hU1]
  have hcu4_ub : (36*Real.pi + 24)⁻¹^4 < (0.007294088:ℝ)^4 := by
    nlinarith [hsq_ub, hup2]
  have hcu4_lb : (0.007294087:ℝ)^4 < (36*Real.pi + 24)⁻¹^4 := by
    nlinarith [hsq_lb, hup2]
  have h17u : (17/2) * (36*Real.pi + 24)⁻¹ < 0.061999748 := by
    have t1 : (17/2) * (36*Real.pi + 24)⁻¹ < (17/2) * 0.007294088 :=
      mul_lt_mul_of_pos_left hu2 (by norm_num : (0:ℝ) < 17/2)
    have t2 : (17/2 : ℝ) * 0.007294088 ≤ 0.061999748 := by norm_num
    exact lt_of_lt_of_le t1 t2
  have h17l : 0.0619997395 < (17/2) * (36*Real.pi + 24)⁻¹ := by
    have t1 : (0.0619997395:ℝ) ≤ (17/2 : ℝ) * 0.007294087 := by norm_num
    have t2 : (17/2) * 0.007294087 < (17/2) * (36*Real.pi + 24)⁻¹ :=
      mul_lt_mul_of_pos_left hu1 (by norm_num : (0:ℝ) < 17/2)
    exact lt_of_le_of_lt t1 t2
  have h12u : 12 * (36*Real.pi + 24)⁻¹^2 < 0.000638447 := by
    have t1 : (12:ℝ) * (36*Real.pi + 24)⁻¹^2 < (12:ℝ) * 0.007294088 ^ 2 :=
      mul_lt_mul_of_pos_left hsq_ub (by norm_num : (0:ℝ) < 12)
    have t2 : (12:ℝ) * 0.007294088 ^ 2 ≤ 0.000638447 := by norm_num
    exact lt_of_lt_of_le t1 t2
  have h12l : 0.000638444 < 12 * (36*Real.pi + 24)⁻¹^2 := by
    have t1 : (0.000638444:ℝ) ≤ (12:ℝ) * 0.007294087 ^ 2 := by norm_num
    have t2 : (12:ℝ) * 0.007294087 ^ 2 < (12:ℝ) * (36*Real.pi + 24)⁻¹ ^ 2 :=
      mul_lt_mul_of_pos_left hsq_lb (by norm_num : (0:ℝ) < 12)
    exact lt_of_le_of_lt t1 t2
  have h72u : 72 * (36*Real.pi + 24)⁻¹^3 < 0.000027942 := by
    have t1 : (72:ℝ) * (36*Real.pi + 24)⁻¹^3 < (72:ℝ) * 0.007294088 ^ 3 :=
      mul_lt_mul_of_pos_left hcu3_ub (by norm_num : (0:ℝ) < 72)
    have t2 : (72:ℝ) * 0.007294088 ^ 3 ≤ 0.000027942 := by norm_num
    exact lt_of_lt_of_le t1 t2
  have h72l : 0.000027941 < 72 * (36*Real.pi + 24)⁻¹^3 := by
    have t1 : (0.000027941:ℝ) ≤ (72:ℝ) * 0.007294087 ^ 3 := by norm_num
    have t2 : (72:ℝ) * 0.007294087 ^ 3 < (72:ℝ) * (36*Real.pi + 24)⁻¹ ^ 3 :=
      mul_lt_mul_of_pos_left hcu3_lb (by norm_num : (0:ℝ) < 72)
    exact lt_of_le_of_lt t1 t2
  have h96u : 96 * (36*Real.pi + 24)⁻¹^4 < 0.000000272 := by
    have t1 : (96:ℝ) * (36*Real.pi + 24)⁻¹^4 < (96:ℝ) * 0.007294088 ^ 4 :=
      mul_lt_mul_of_pos_left hcu4_ub (by norm_num : (0:ℝ) < 96)
    have t2 : (96:ℝ) * 0.007294088 ^ 4 ≤ 0.000000272 := by norm_num
    exact lt_of_lt_of_le t1 t2
  have h96l : 0.000000271 < 96 * (36*Real.pi + 24)⁻¹^4 := by
    have t1 : (0.000000271:ℝ) ≤ (96:ℝ) * 0.007294087 ^ 4 := by norm_num
    have t2 : (96:ℝ) * 0.007294087 ^ 4 < (96:ℝ) * (36*Real.pi + 24)⁻¹ ^ 4 :=
      mul_lt_mul_of_pos_left hcu4_lb (by norm_num : (0:ℝ) < 96)
    exact lt_of_le_of_lt t1 t2
  have e1 : 17 / (2 * (36*Real.pi + 24)) = (17/2) * (36*Real.pi + 24)⁻¹ := by field_simp
  have e2 : 12 / (36*Real.pi + 24)^2 = 12 * (36*Real.pi + 24)⁻¹^2 := by field_simp
  have e3 : 72 / (36*Real.pi + 24)^3 = 72 * (36*Real.pi + 24)⁻¹^3 := by field_simp
  have e4 : 96 / (36*Real.pi + 24)^4 = 96 * (36*Real.pi + 24)⁻¹^4 := by field_simp
  have hSlow : (137.03600185:ℝ) < 36*Real.pi + 24 - (17/2)*(36*Real.pi + 24)⁻¹
      + 12*(36*Real.pi + 24)⁻¹^2 + 72*(36*Real.pi + 24)⁻¹^3
      - 96*(36*Real.pi + 24)⁻¹^4 := by
    linarith [hA1, h17u, h12l, h72l, h96u]
  have hShigh : 36*Real.pi + 24 - (17/2)*(36*Real.pi + 24)⁻¹
      + 12*(36*Real.pi + 24)⁻¹^2 + 72*(36*Real.pi + 24)⁻¹^3
      - 96*(36*Real.pi + 24)⁻¹^4 < 137.036002 := by
    linarith [hA2, h17l, h12u, h72u, h96l]
  unfold serieRadiativa
  rw [e1, e2, e3, e4]
  exact ⟨le_of_lt hSlow, hShigh⟩

/-- **M2 — cota rigurosa**: |serieRadiativa − 137.036| < 2·10⁻⁶. -/
theorem serie_cota_pi : |serieRadiativa - 137.036| < 0.000002 := by
  obtain ⟨h1, h2⟩ := serieRadiativa_acotada
  rw [abs_lt]
  constructor <;> linarith

/-- **M2 — precisión de 9 cifras**: certifica el valor 137.0360019 del libro. -/
theorem serie_precision : |serieRadiativa - 137.0360019| < 0.0000001 := by
  obtain ⟨h1, h2⟩ := serieRadiativa_acotada
  rw [abs_lt]
  constructor <;> linarith

/-- **M2 — contraste con CODATA**: la serie truncada a 4 bucles da 137.0360019,
    a 2.8·10⁻⁶ del valor experimental 137.035999177 (CODATA). -/
theorem serie_vs_CODATA :
    |serieRadiativa - 137.035999177| < 0.000003 := by
  obtain ⟨h1, h2⟩ := serieRadiativa_acotada
  rw [abs_lt]
  constructor <;> linarith

/-! ## E-40 — nucleo verificable (base + F1 + F2) vs cola (F3, F4)

El nucleo de la serie es la base mas los dos primeros terminos (F3,F4 excluidos):
verificable con tres conteos independientes (base 12(3pi+2), F1=17, F2=12) y dos
cierres. F3 y F4 afinan a 0.0199 ppm pero NO son discriminantes. -/

/-- El nucleo (dos terminos): A - F1/(2A) + F2/A^2, con A = 36pi + 24. -/
noncomputable def serieNucleo : ℝ :=
  (36*Real.pi + 24) - 17/(2*(36*Real.pi + 24)) + 12/(36*Real.pi + 24)^2

/-- **E-40 — cota del nucleo**: la serie truncada a dos terminos queda en
    (137.03597, 137.03598) (el valor 137.035974 del libro, error 0.18 ppm). -/
theorem serieNucleo_acotada :
    (137.03597:ℝ) ≤ serieNucleo ∧ serieNucleo < 137.03598 := by
  have hA1 : (137.09733552:ℝ) < 36 * Real.pi + 24 := by have := Real.pi_gt_d20; linarith
  have hA2 : 36 * Real.pi + 24 < 137.09733553 := by have := Real.pi_lt_d20; linarith
  have hApos : (0:ℝ) < 36 * Real.pi + 24 := lt_trans (by norm_num) hA1
  have hu1 : (0.007294087:ℝ) < (36*Real.pi + 24)⁻¹ := by
    rw [← one_div, lt_div_iff₀ hApos]
    have h1 : (0.007294087:ℝ) * (36*Real.pi + 24) < 0.007294087 * 137.09733553 := mul_lt_mul_of_pos_left hA2 (by norm_num)
    have h2 : (0.007294087:ℝ) * 137.09733553 ≤ 1 := by norm_num
    linarith
  have hu2 : (36*Real.pi + 24)⁻¹ < 0.007294088 := by
    rw [← one_div, div_lt_iff₀ hApos]
    have h1 : (1:ℝ) < 0.007294088 * 137.09733552 := by norm_num
    have h2 : (0.007294088:ℝ) * 137.09733552 < 0.007294088 * (36*Real.pi + 24) := mul_lt_mul_of_pos_left hA1 (by norm_num)
    linarith
  have hsq_ub : (36*Real.pi + 24)⁻¹^2 < (0.007294088:ℝ)^2 := by
    rw [pow_two, pow_two]
    have hup : (0:ℝ) < (36*Real.pi+24)⁻¹ := by positivity
    have s1 := mul_lt_mul_of_pos_right hu2 hup
    have s2 := mul_lt_mul_of_pos_left hu2 (by norm_num : (0:ℝ) < 0.007294088)
    linarith [s1, s2]
  have hsq_lb : (0.007294087:ℝ)^2 < (36*Real.pi + 24)⁻¹^2 := by
    rw [pow_two, pow_two]
    have hup : (0:ℝ) < (36*Real.pi+24)⁻¹ := by positivity
    have s1 := mul_lt_mul_of_pos_left hu1 (by norm_num : (0:ℝ) < 0.007294087)
    have s2 := mul_lt_mul_of_pos_right hu1 hup
    linarith [s1, s2]
  have h17u : (17/2) * (36*Real.pi + 24)⁻¹ < 0.061999748 := by
    have t1 := mul_lt_mul_of_pos_left hu2 (by norm_num : (0:ℝ) < 17/2); nlinarith [t1]
  have h17l : 0.0619997395 < (17/2) * (36*Real.pi + 24)⁻¹ := by
    have t1 : (0.0619997395:ℝ) ≤ (17/2 : ℝ) * 0.007294087 := by norm_num
    have t2 := mul_lt_mul_of_pos_left hu1 (by norm_num : (0:ℝ) < 17/2)
    linarith [t1, t2]
  have h12u : 12 * (36*Real.pi + 24)⁻¹^2 < 0.000638447 := by
    have t1 := mul_lt_mul_of_pos_left hsq_ub (by norm_num : (0:ℝ) < 12); nlinarith [t1]
  have h12l : 0.000638444 < 12 * (36*Real.pi + 24)⁻¹^2 := by
    have t1 : (0.000638444:ℝ) ≤ (12:ℝ) * 0.007294087^2 := by norm_num
    have t2 := mul_lt_mul_of_pos_left hsq_lb (by norm_num : (0:ℝ) < 12)
    linarith [t1, t2]
  have e1 : 17 / (2 * (36*Real.pi + 24)) = (17/2) * (36*Real.pi + 24)⁻¹ := by field_simp
  have e2 : 12 / (36*Real.pi + 24)^2 = 12 * (36*Real.pi + 24)⁻¹^2 := by field_simp
  unfold serieNucleo
  rw [e1, e2]
  constructor
  · linarith [hA1, h17u, h12l]
  · linarith [hA2, h17l, h12u]

end TIE
