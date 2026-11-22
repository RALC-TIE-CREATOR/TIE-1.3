/-
TIE — Teoría del Tiempo (Cap. 1), paso T7c: campo ρ_I dipolar (sector rotacional)

Infraestructura analítica en `E3 = EuclideanSpace ℝ (Fin 3)`:
  · `crossE`  — producto vectorial (coacción desde `crossProduct` de Mathlib).
  · `curlE`   — rotacional por componentes vía `fderiv`.
  · `rhoIDipole`, `AgDipole`, `gradRhoIDipole` — los campos del dipolo.

**Certificado (sin `sorry`):**
  · T7c-1 — gradiente explícito de `ρ_I`: `∇ρ_I = (G/c⁴)[J − 3(J·x̂)x̂]/‖x‖³` (`rhoIDipole_grad`).

**EN CURSO (WIP, a terminar; NO cerrado; ver T7C3_WIP.md):**
  · T7c-2 — identidad del rotacional del dipolo.
  · T7c-3 — armonicidad de rho_I; crux aislado (ver T7C3_WIP.md).
  · T7c-4 — `∇×A_g = 2c²∇ρ_I`.
Ver `MATHLIB_API_RHO_I.md`.
-/
import Mathlib
import TieFormal.Primitivos

namespace TIE
open TieFormal

/-- Espacio euclídeo 3D. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Producto vectorial en `E3` (coacción del `crossProduct` de Mathlib, que vive en `Fin 3 → ℝ`). -/
noncomputable def crossE (u v : E3) : E3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

/-- Isometría lineal continua `E3 ≃ (Fin 3 → ℝ)` (para el producto vectorial). -/
noncomputable def E3lp : E3 ≃L[ℝ] (Fin 3 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- Producto vectorial `u × ·` como aplicación lineal **continua**. -/
noncomputable def crossECLM (u : E3) : E3 →L[ℝ] E3 :=
  (E3lp.symm).toContinuousLinearMap.comp
    (((crossProduct (E3lp u)).toContinuousLinearMap).comp E3lp.toContinuousLinearMap)

/-- `crossECLM u v = crossE u v`. -/
theorem crossECLM_apply (u v : E3) : crossECLM u v = crossE u v := by
  simp only [crossECLM, crossE, E3lp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

/-- **Rotacional** en `E3`, por componentes vía `fderiv`: `(∇×F)ᵢ = ε_{ijk} ∂_j F_k`. -/
noncomputable def curlE (F : E3 → E3) (x : E3) : E3 :=
  let L := fderiv ℝ F x
  let d (j : Fin 3) : Fin 3 → ℝ := (L (EuclideanSpace.single j 1)).ofLp
  WithLp.toLp 2 ![(d 1) 2 - (d 2) 1, (d 2) 0 - (d 0) 2, (d 0) 1 - (d 1) 0]

/-- **Campo de densidad de información (dipolo):** `ρ_I(x) = (G/c⁴)(J·x)/‖x‖³`. -/
noncomputable def rhoIDipole (P : PrimitivosTIE) (J x : E3) : ℝ :=
  (P.G / P.c ^ 4) * (inner ℝ J x) * (‖x‖ ^ 3)⁻¹

/-- **Potencial vectorial gravitomagnético:** `A_g(x) = −(2G/c²)(J×x)/‖x‖³`. -/
noncomputable def AgDipole (P : PrimitivosTIE) (J x : E3) : E3 :=
  -(((2 * P.G) / P.c ^ 2) * (‖x‖ ^ 3)⁻¹) • crossE J x

/-- **Gradiente explícito de `ρ_I`:** `∇ρ_I(x) = (G/c⁴)[J − 3(J·x̂)x̂]/‖x‖³`. -/
noncomputable def gradRhoIDipole (P : PrimitivosTIE) (J x : E3) : E3 :=
  ((P.G / P.c ^ 4) * (‖x‖ ^ 3)⁻¹) • (J - ((3 : ℝ) * (inner ℝ J x) * (‖x‖ ^ 2)⁻¹) • x)

/-! ### Helpers rpow ↔ potencia natural -/

theorem rpow32 (y : E3) : (‖y‖ ^ 2) ^ (-(3/2:ℝ)) = (‖y‖ ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast (‖y‖) 2, ← Real.rpow_mul (norm_nonneg y)]
  rw [show ((2:ℕ):ℝ) * (-(3/2:ℝ)) = -3 by norm_num]
  rw [Real.rpow_neg (norm_nonneg y), Real.rpow_ofNat]

theorem rpow52 (y : E3) : (‖y‖ ^ 2) ^ (-(5/2:ℝ)) = (‖y‖ ^ 5)⁻¹ := by
  rw [← Real.rpow_natCast (‖y‖) 2, ← Real.rpow_mul (norm_nonneg y)]
  rw [show ((2:ℕ):ℝ) * (-(5/2:ℝ)) = -5 by norm_num]
  rw [Real.rpow_neg (norm_nonneg y), Real.rpow_ofNat]

/-- **T7c-1.** Gradiente explícito del dipolo `ρ_I`: para `x ≠ 0`,
    `fderiv ℝ (rhoIDipole P J) x = innerSL ℝ (gradRhoIDipole P J x)`
    (equivalente a `∇ρ_I = (G/c⁴)[J − 3(J·x̂)x̂]/‖x‖³`). -/
theorem rhoIDipole_grad (P : PrimitivosTIE) (J x : E3) (hx : x ≠ 0) :
    ∀ v : E3, fderiv ℝ (rhoIDipole P J) x v = inner ℝ (gradRhoIDipole P J x) v := by
  intro v
  set k : ℝ := P.G / P.c ^ 4 with hk
  have hfun : rhoIDipole P J
      = fun y : E3 => k * (inner ℝ J y) * ((‖y‖ ^ 2) ^ (-(3/2:ℝ))) := by
    funext y
    rw [rhoIDipole, hk, ← rpow32 y]
  rw [hfun]
  have hnsq_pos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hgn : HasFDerivAt (fun y : E3 => inner ℝ J y) (innerSL ℝ J) x :=
    ContinuousLinearMap.hasFDerivAt (innerSL ℝ J)
  have hg : HasFDerivAt (fun y : E3 => k * (inner ℝ J y)) (k • innerSL ℝ J) x :=
    hgn.const_mul k
  have hh : HasFDerivAt (fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)))
      (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) • (2 • innerSL ℝ x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-(3/2:ℝ)))
        ((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) (‖x‖ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hnsq_pos))
    have h2 : HasFDerivAt (fun y : E3 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
      have hd : DifferentiableAt ℝ (fun y : E3 => ‖y‖ ^ 2) x := by
        have hint : DifferentiableAt ℝ (fun y : E3 => inner ℝ y y) x :=
          DifferentiableAt.inner ℝ (differentiableAt_id (x := x)) (differentiableAt_id (x := x))
        simpa only [real_inner_self_eq_norm_sq] using hint
      have h2' := hd.hasFDerivAt
      rwa [fderiv_norm_sq_apply] at h2'
    exact h1.comp_hasFDerivAt x h2
  have hfderiv : fderiv ℝ (fun y : E3 => k * (inner ℝ J y) * (‖y‖ ^ 2) ^ (-(3/2:ℝ))) x
      = ((k * (inner ℝ J x)) • (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) • (2 • innerSL ℝ x)))
        + ((‖x‖ ^ 2) ^ (-(3/2:ℝ)) • (k • innerSL ℝ J)) :=
    (hg.mul hh).fderiv
  rw [hfderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [gradRhoIDipole, hk]
  simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
  rw [show (-(3/2:ℝ) - 1) = (-(5/2:ℝ)) by norm_num, rpow32 x, rpow52 x]
  have h5 : (‖x‖ ^ 5)⁻¹ = (‖x‖ ^ 3)⁻¹ * (‖x‖ ^ 2)⁻¹ := by
    rw [show (5:ℕ) = 3 + 2 by norm_num, pow_add]; ring
  rw [h5]; ring


/-- **T7c-2 (paso 1).** `fderiv` de `F = (‖·‖³)⁻¹ • (J×·)`:
    `fderiv F x = (‖x‖³)⁻¹ • crossECLM J + ((-3‖x‖⁻⁵) • innerSL x).smulRight (J×x)`. -/
theorem fderiv_curl_dipole (J x : E3) (hx : x ≠ 0) :
    fderiv ℝ (fun y : E3 => (‖y‖ ^ 3)⁻¹ • crossE J y) x
      = (‖x‖ ^ 3)⁻¹ • crossECLM J
        + (((-3 : ℝ) * (‖x‖ ^ 2) ^ (-(5/2:ℝ))) • innerSL ℝ x).smulRight (crossE J x) := by
  have hfun : (fun y : E3 => (‖y‖ ^ 3)⁻¹ • crossE J y)
      = fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)) • crossE J y := by
    funext y; rw [← rpow32 y]
  rw [hfun]
  have hnsq_pos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hs : HasFDerivAt (fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)))
      (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) • (2 • innerSL ℝ x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-(3/2:ℝ)))
        ((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) (‖x‖ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hnsq_pos))
    have h2 : HasFDerivAt (fun y : E3 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
      have hd : DifferentiableAt ℝ (fun y : E3 => ‖y‖ ^ 2) x := by
        have hint : DifferentiableAt ℝ (fun y : E3 => inner ℝ y y) x :=
          DifferentiableAt.inner ℝ (differentiableAt_id (x := x)) (differentiableAt_id (x := x))
        simpa only [real_inner_self_eq_norm_sq] using hint
      have h2' := hd.hasFDerivAt
      rwa [fderiv_norm_sq_apply] at h2'
    exact h1.comp_hasFDerivAt x h2
  have hc : HasFDerivAt (fun y : E3 => crossE J y) (crossECLM J) x := by
    have h1 : HasFDerivAt (fun y : E3 => crossECLM J y) (crossECLM J) x :=
      ContinuousLinearMap.hasFDerivAt (crossECLM J)
    have h2 : (fun y : E3 => crossECLM J y) = fun y : E3 => crossE J y := by
      funext y; exact crossECLM_apply J y
    rwa [h2] at h1
  have hprod := hs.smul hc
  rw [show fderiv ℝ (fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)) • crossE J y) x
        = (‖x‖ ^ 2) ^ (-(3/2:ℝ)) • crossECLM J
          + (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) • (2 • innerSL ℝ x)).smulRight
              (crossE J x)
        from hprod.fderiv]
  rw [show (-(3/2:ℝ) - 1) = (-(5/2:ℝ)) by norm_num, rpow32 x]
  have hclm : (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(5/2:ℝ))) • (2 • innerSL ℝ x))
      = ((-3 : ℝ) * (‖x‖ ^ 2) ^ (-(5/2:ℝ))) • innerSL ℝ x := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  rw [hclm]


/-- **T7c-2.** Rotacional del dipolo:
    `∇×[(J×x)/‖x‖³] = −J/‖x‖³ + 3(J·x)x/‖x‖⁵`
    (signo corregido 2026-09-16; el enunciado previo con `+J` estaba invertido). -/
theorem curl_dipole (J x : E3) (hx : x ≠ 0) :
    curlE (fun y : E3 => (‖y‖ ^ 3)⁻¹ • crossE J y) x
      = -(‖x‖ ^ 3)⁻¹ • J + ((3 : ℝ) * (inner ℝ J x) * (‖x‖ ^ 5)⁻¹) • x := by
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hns : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq x, PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, Fin.sum_univ_one]
    ring
  rw [curlE, fderiv_curl_dipole J x hx]
  ext i
  fin_cases i <;>
    simp only [crossECLM_apply, crossE, PiLp.single_apply, WithLp.ofLp_toLp, WithLp.toLp_ofLp,
      cross_apply, Pi.single_eq_same, Pi.single_eq_of_ne, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul,
      Matrix.cons_val, PiLp.inner_apply, Fin.isValue, Fin.sum_univ_three] <;>
    norm_num <;>
    rw [rpow52 x] <;>
    field_simp <;>
    rw [← hns] <;>
    ring

theorem curlE_const_smul (a : ℝ) (F : E3 → E3) (x : E3) (hF : DifferentiableAt ℝ F x) :
    curlE (fun y => a • F y) x = a • curlE F x := by
  simp only [curlE]
  rw [show fderiv ℝ (fun y : E3 => a • F y) x = fderiv ℝ (a • F) x from rfl,
      fderiv_const_smul hF a]
  ext i
  fin_cases i <;> simp only [WithLp.ofLp_smul, Pi.smul_apply] <;> simp <;> ring

theorem curl_Ag (P : PrimitivosTIE) (J x : E3) (hx : x ≠ 0) :
    curlE (AgDipole P J) x = (2 * P.c ^ 2) • gradRhoIDipole P J x := by
  have hnsq_pos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hs : HasFDerivAt (fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)))
      (((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) • (2 • innerSL ℝ x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-(3/2:ℝ)))
        ((-(3/2:ℝ)) * (‖x‖ ^ 2) ^ (-(3/2:ℝ) - 1)) (‖x‖ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hnsq_pos))
    have h2 : HasFDerivAt (fun y : E3 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
      have hd : DifferentiableAt ℝ (fun y : E3 => ‖y‖ ^ 2) x := by
        have hint : DifferentiableAt ℝ (fun y : E3 => inner ℝ y y) x :=
          DifferentiableAt.inner ℝ (differentiableAt_id (x := x)) (differentiableAt_id (x := x))
        simpa only [real_inner_self_eq_norm_sq] using hint
      have h2' := hd.hasFDerivAt
      rwa [fderiv_norm_sq_apply] at h2'
    exact h1.comp_hasFDerivAt x h2
  have hc : HasFDerivAt (fun y : E3 => crossE J y) (crossECLM J) x := by
    have h1 : HasFDerivAt (fun y : E3 => crossECLM J y) (crossECLM J) x :=
      ContinuousLinearMap.hasFDerivAt (crossECLM J)
    have h2 : (fun y : E3 => crossECLM J y) = fun y : E3 => crossE J y := by
      funext y; exact crossECLM_apply J y
    rwa [h2] at h1
  have hF' : DifferentiableAt ℝ (fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)) • crossE J y) x :=
    (hs.smul hc).differentiableAt
  have hF : DifferentiableAt ℝ (fun y : E3 => (‖y‖ ^ 3)⁻¹ • crossE J y) x := by
    rw [show (fun y : E3 => (‖y‖ ^ 3)⁻¹ • crossE J y)
        = fun y : E3 => (‖y‖ ^ 2) ^ (-(3/2:ℝ)) • crossE J y from by
          funext y; rw [← rpow32 y]]
    exact hF'
  have hAg : AgDipole P J
      = fun y : E3 => (-(2 * P.G / P.c ^ 2)) • ((‖y‖ ^ 3)⁻¹ • crossE J y) := by
    funext y
    rw [AgDipole]
    simp only [neg_mul, smul_smul]
  rw [hAg, curlE_const_smul _ _ _ hF, curl_dipole J x hx]
  rw [gradRhoIDipole]
  have hc0 : P.c ≠ 0 := P.c_ne
  have h5 : (‖x‖ ^ 5)⁻¹ = (‖x‖ ^ 3)⁻¹ * (‖x‖ ^ 2)⁻¹ := by
    rw [show (5:ℕ) = 3 + 2 by norm_num, pow_add]; ring
  rw [h5]
  ext i
  fin_cases i <;>
    simp only [Pi.smul_apply, smul_add, neg_smul, smul_neg, smul_smul] <;>
    field_simp <;>
    simp <;>
    ring


end TIE
