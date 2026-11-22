/-
TIE — Ticket T01 (Bisturí v4.0): núcleo formal — P1 (π-TIE), P2 (adimensionalización),
P3 (conteos finos de Γ₂₁ + aritmética de α). Generado con datos de b02_validacion_v4.py.
-/
import Mathlib
import TieFormal.TMTGamma21
namespace TIE.TMT

/-! ### P1 — Sistema π-TIE: identidades algebraicas (ω_z=π/τ, c=πa/τ, ħ=m₀ω_z a², G=ω_z²a³/(2πm₀)) -/
theorem p1_c_def (a τ : ℝ) : Real.pi * a / τ = (Real.pi / τ) * a := by ring
theorem p1_hbar (a τ m0 : ℝ) : m0 * (Real.pi / τ) * a^2 = Real.pi * m0 * a^2 / τ := by ring
theorem p1_G (a τ m0 : ℝ) (hτ : τ ≠ 0) (hm0 : m0 ≠ 0) :
    (Real.pi / τ)^2 * a^3 / (2 * Real.pi * m0) = Real.pi * a^3 / (2 * τ^2 * m0) := by
  field_simp
  try ring
/-! **Refutación (erratas del ticket)**: `ħ = πm₀a³/τ` y `G = πa⁵/(2τ²m₀)` son FALSAS (el exponente correcto es a² y a³ respectivamente; contraejemplo a=2, τ=1, m₀=1). -/
theorem p1_hbar_errata : ¬ (∀ a τ m0 : ℝ, m0 * (Real.pi / τ) * a^2 = Real.pi * m0 * a^3 / τ) := by
  intro h
  have h2 := h 2 1 1
  field_simp [Real.pi_ne_zero] at h2
  nlinarith [Real.pi_pos]
theorem p1_G_errata : ¬ (∀ a τ m0 : ℝ, (Real.pi / τ)^2 * a^3 / (2 * Real.pi * m0) = Real.pi * a^5 / (2 * τ^2 * m0)) := by
  intro h
  have h2 := h 2 1 1
  field_simp [Real.pi_ne_zero] at h2
  nlinarith [Real.pi_pos]
/-! **Monomialidad (P1-d)**: las derivadas son monomios π^s a^p τ^q m₀^r — formas exhibidas arriba (c: a¹τ⁻¹π¹; ħ: a²τ⁻¹m₀¹π¹; G: a³τ⁻²m₀⁻¹π¹/2). -/

/-! ### P2 — Adimensionalización: E=Ẽm₀c², p=p̃m₀c, m=Nm₀ ⇒ E²=(pc)²+(mc²)² ⟺ Ẽ²=p̃²+N² -/
theorem p2 (e pp N : ℝ) (c m0 : ℝ) (hc : c ≠ 0) (hm : m0 ≠ 0) :
    ((e*m0*c^2)^2 = (pp*m0*c^2)^2 + (N*m0*c^2)^2) ↔ (e^2 = pp^2 + N^2) := by
  have h4 : (m0*c^2)^2 ≠ 0 := by positivity
  constructor
  · intro h
    have h' : (m0*c^2)^2 * e^2 = (m0*c^2)^2 * (pp^2 + N^2) := by nlinarith [h]
    exact mul_left_cancel₀ h4 h'
  · intro h
    calc (e*m0*c^2)^2 = (m0*c^2)^2 * e^2 := by ring
      _ = (m0*c^2)^2 * (pp^2 + N^2) := by rw [h]
      _ = (pp*m0*c^2)^2 + (N*m0*c^2)^2 := by ring

/-! ### P3 — Conteos finos de Γ₂₁ + α -/
/-! **(a)** F₁ = β₀+β₁ = 1+16 = 17. -/
theorem p3_F1 : (1:ℕ) + 16 = 17 := by norm_num

/-! **(b)** Partición kink/antikink de las 24 plaquetas (tetA={0,3,5,6} vs tetB). -/
def plaqSign : List ℤ := [1, 1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1]
theorem p3_split : ((plaqSign.filter (fun s => s = 1)).length = 12) ∧ ((plaqSign.filter (fun s => s = -1)).length = 12) := by decide

/-! **(c-d)** Plaquetas (4 aristas cada una; códigos arista = min·100+max) → F₃=72 pares que comparten arista; F₄=Σ bordes=96=24·4. -/
def plaqEdges : List (List ℕ) :=
  [[8, 9, 820, 920],
   [8, 10, 820, 1020],
   [9, 10, 920, 1020],
   [108, 111, 820, 1120],
   [108, 112, 820, 1220],
   [111, 112, 1120, 1220],
   [209, 213, 920, 1320],
   [209, 214, 920, 1420],
   [213, 214, 1320, 1420],
   [311, 313, 1120, 1320],
   [311, 315, 1120, 1520],
   [313, 315, 1320, 1520],
   [410, 416, 1020, 1620],
   [410, 417, 1020, 1720],
   [416, 417, 1620, 1720],
   [512, 516, 1220, 1620],
   [512, 518, 1220, 1820],
   [516, 518, 1620, 1820],
   [614, 617, 1420, 1720],
   [614, 619, 1420, 1920],
   [617, 619, 1720, 1920],
   [715, 718, 1520, 1820],
   [715, 719, 1520, 1920],
   [718, 719, 1820, 1920]]
theorem p3_F4 : (plaqEdges.map List.length).sum = 96 ∧ (96 = 24 * 4) := by decide
theorem p3_F3 :
    (((List.range 24).product (List.range 24)).filter (fun p =>
      p.1 < p.2 ∧ (plaqEdges.getD p.1 []).any (fun e => (plaqEdges.getD p.2 []).contains e))).length = 72 := by
  decide
theorem p3_edges_dedup : (plaqEdges.flatten).dedup.length = 36 := by decide

/-! **(e)** Cota de α⁻¹ = A − F₁/(2A) + F₂/A² + F₃/A³ − F₄/A⁴ (A=36π+24; F₂=12 el split). -/
theorem p3_alpha :
    (137.0359 : ℝ) < 36*Real.pi + 24 - 17/(2*(36*Real.pi + 24)) + 12/(36*Real.pi + 24)^2 + 72/(36*Real.pi + 24)^3 - 96/(36*Real.pi + 24)^4 ∧
    36*Real.pi + 24 - 17/(2*(36*Real.pi + 24)) + 12/(36*Real.pi + 24)^2 + 72/(36*Real.pi + 24)^3 - 96/(36*Real.pi + 24)^4 < 137.0361 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hA1 : (137.097312 : ℝ) < 36*Real.pi + 24 := by linarith
  have hA2 : 36*Real.pi + 24 < (137.097348 : ℝ) := by linarith
  have t1 : 17/(2*(36*Real.pi + 24)) < (17/274.194624 : ℝ) := by
    gcongr <;> linarith
  have u1 : (17/274.194696 : ℝ) < 17/(2*(36*Real.pi + 24)) := by
    gcongr <;> linarith
  have t2 : (12/(137.097348^2) : ℝ) < 12/(36*Real.pi + 24)^2 := by gcongr <;> linarith
  have u2 : 12/(36*Real.pi + 24)^2 < (12/(137.097312^2) : ℝ) := by gcongr <;> linarith
  have t3 : (72/(137.097348^3) : ℝ) < 72/(36*Real.pi + 24)^3 := by gcongr <;> linarith
  have u3 : 72/(36*Real.pi + 24)^3 < (72/(137.097312^3) : ℝ) := by gcongr <;> linarith
  have t4 : (96/(36*Real.pi + 24)^4) < (96/(137.097312^4) : ℝ) := by gcongr <;> linarith
  have u4 : (96/(137.097348^4) : ℝ) < 96/(36*Real.pi + 24)^4 := by gcongr <;> linarith
  have hlow : (137.0359 : ℝ) < 137.097312 - 17/274.194624 + 12/137.097348^2 + 72/137.097348^3 - 96/137.097312^4 := by norm_num
  have hhigh : 137.097348 - 17/274.194696 + 12/137.097312^2 + 72/137.097312^3 - 96/137.097348^4 < (137.0361 : ℝ) := by norm_num
  constructor
  · linarith [hA1, t1, t2, t3, t4, hlow]
  · linarith [hA2, u1, u2, u3, u4, hhigh]
end TIE.TMT