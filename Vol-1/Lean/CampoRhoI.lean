/-
TIE — Teoría del Tiempo (Cap. 1), paso T7: campo de densidad de información ρ_I
Módulo unificado: álgebra vectorial + puente h₀↔A_g + álgebra del acoplamiento espín–ρ_I.

Certifica:
  · Álgebra vectorial de la precesión de Lense–Thirring (TT15).
  · Puente definicional `A_g := −c·h₀` (cierre estructural del paso (b) de R1).
  · Factor `c²` del acoplamiento `L_int = +c² S·∇ρ_I` (R1, no postulado; acoplamiento giroscópico `+½ S·B_g`).
  · Signo del Hamiltoniano `H_int = +S·Ω_LT` (matiz 2).

La identidad diferencial del dipolo `∇×[(J×r)/r³] = [3r̂(J·r̂) − J]/r³` y la
armónicidad `Δρ_I = 0` están **verificadas simbólicamente** (`sympy`;
VERIFICACION_SYMPY_RHO_I.py). Su formalización en Lean queda como **programa
pendiente declarado** (Mathlib no provee `curl`/`divergence`; la 2ª derivada de
`fderiv` para `(J·x)/‖x‖³` exige un montaje considerable).
-/
import Mathlib

namespace TIE

/-- Vector en ℝ³ (representado como par anidado: `ℝ × (ℝ × ℝ)`). -/
abbrev V3 := ℝ × ℝ × ℝ

/-- Producto punto en ℝ³. -/
def dot3 (u v : V3) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Producto vectorial en ℝ³. -/
def cross3 (u v : V3) : V3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

/-- Multiplicación escalar por vector (componente a componente). -/
def smul3 (a : ℝ) (v : V3) : V3 := (a * v.1, a * v.2.1, a * v.2.2)

/-- **TT15**: el torque `τ = Ω × S` es ortogonal al espín `S` (la precesión
    no cambia `|S|`). -/
theorem torque_orthogonal_spin (Ω S : V3) : dot3 (cross3 Ω S) S = 0 := by
  simp [dot3, cross3]; ring

/-- El torque también es ortogonal al eje de precesión `Ω`. -/
theorem torque_orthogonal_axis (Ω S : V3) : dot3 (cross3 Ω S) Ω = 0 := by
  simp [dot3, cross3]; ring

/-- El producto triple escalar es invariante cíclico: `u·(v×w) = (u×v)·w`. -/
theorem scalar_triple_cyclic (u v w : V3) :
    dot3 u (cross3 v w) = dot3 (cross3 u v) w := by
  simp [dot3, cross3]; ring

/-- El producto vectorial es antisimétrico: `u×v = −(v×u)`. -/
theorem cross3_antisym (u v : V3) : cross3 u v + cross3 v u = (0, 0, 0) := by
  ext <;> simp [cross3] <;> ring

/-! ### (b) El puente shift ↔ A_g (TT14.3)

`h_{0i} = −A_{g,i}/c`, es decir `A_g = −c·h₀`. Se adopta como **definición**
(reorganización del shift), no como hipótesis independiente. -/

/-- Potencial gravitomagnético en función del shift: `A_g = −c·h₀` (definición). -/
def AgOf (c : ℝ) (h0 : V3) : V3 := smul3 (-c) h0

/-- **Puente (b).** `h₀ = −A_g/c` (inversa de `AgOf`), con `c ≠ 0`. -/
theorem bridge_h0 (c : ℝ) (h0 : V3) (hc : c ≠ 0) :
    h0 = smul3 (-(1 / c)) (AgOf c h0) := by
  simp only [AgOf, smul3]
  ext <;> field_simp

/-! ### R1 — factor del acoplamiento espín–ρ_I (derivado, no postulado)

En R1 el acoplamiento `L_int = +c² S·∇ρ_I` **no se postula**: es el acoplamiento
giroscópico `L_int = +½ S·B_g` (factor `½` = factor giroscópico del PPN) reescrito
con el puente `B_g = 2c²∇ρ_I` (TT14.7). -/

/-- Campo gravitomagnético: `B_g = 2c²∇ρ_I` (TT14.7). -/
def BgOf (c : ℝ) (g : V3) : V3 := smul3 (2 * c^2) g

/-- Precesión de Lense–Thirring (prógrada, E-2): `Ω_LT = +c²∇ρ_I`. -/
def OmegaLT (c : ℝ) (g : V3) : V3 := smul3 (c^2) g

/-- **R1 (factor).** `−½ S·B_g = −c² S·∇ρ_I`: el factor `c²` sale de `½ × 2c²`. -/
theorem rhoI_coupling_factor (c : ℝ) (S g : V3) :
    (1/2) * dot3 S (BgOf c g) = (c^2) * dot3 S g := by
  simp [dot3, BgOf, smul3]; ring

/-- **R1 (Ω_LT ↔ B_g).** `Ω_LT = +½ B_g`. -/
theorem OmegaLT_eq_pos_half_Bg (c : ℝ) (g : V3) :
    OmegaLT c g = smul3 (1/2) (BgOf c g) := by
  simp only [OmegaLT, BgOf, smul3]
  ext <;> ring

/-- **R1 (torque).** `τ = Ω_LT × S = +c² (∇ρ_I × S)`. -/
theorem rhoI_tau_factor (c : ℝ) (S g : V3) :
    cross3 (OmegaLT c g) S = smul3 (c^2) (cross3 g S) := by
  ext <;> simp only [cross3, OmegaLT, smul3] <;> ring

/-- **R1 (conservación).** La precesión `τ = Ω_LT × S` es ortogonal a `S` (`|S|` constante). -/
theorem rhoI_precession_orthogonal (c : ℝ) (S g : V3) :
    dot3 (cross3 (OmegaLT c g) S) S = 0 :=
  torque_orthogonal_spin (OmegaLT c g) S

/-! ### Matiz 2 — signo del acoplamiento (corchetes de Poisson)

Con `{S_i,S_j}=ε_{ijk}S_k`, el Hamiltoniano `H = Ω·S` genera `Ṡ = Ω × S` (no `−Ω × S`). -/

/-- Corchete de Poisson de funciones lineales del espín: `{a·S, b·S} = (a×b)·S`. -/
def spinBracket (a b S : V3) : ℝ := dot3 (cross3 a b) S

/-- **Signo del acoplamiento.** Con `H = Ω·S`, `Ṡ_i = {S_i,H} = (Ω×S)_i`; el signo
    `+S·Ω_LT` (no `−S·Ω_LT`) reproduce la precesión de Lense–Thirring. -/
theorem hamiltonian_sign (Ω S : V3) :
    spinBracket (1, 0, 0) Ω S = (cross3 Ω S).1
    ∧ spinBracket (0, 1, 0) Ω S = (cross3 Ω S).2.1
    ∧ spinBracket (0, 0, 1) Ω S = (cross3 Ω S).2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [spinBracket, dot3, cross3] <;> ring

end TIE
