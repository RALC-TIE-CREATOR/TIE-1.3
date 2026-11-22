/-
TIE M6 — Álgebra del marco: el modo puro gauge (corrección TT24)

Contenido matemático de TT24: el tensor de Ricci linealizado de una perturbación
puro-gauge h_μν = ∂_μξ_ν + ∂_νξ_μ se anula idénticamente. Esto certifica el
mecanismo "pure gauge" que sustenta la corrección de TT24 (el modo de norma no
genera curvatura lineal; de ahí que el punto de control dé G₀₀ = 0 y el residuo
adopte la forma A(t) = a·t + b, es decir, sin contenido físico adicional).

Formalización autocontenida: polinomios multivariados (MvPolynomial) sobre ℝ con
la signatura η = diag(−1, 1, 1, 1) y las derivadas parciales formales ∂_μ. Se
prueba por cálculo de coeficientes (inducción sobre monomios + `ring`).
-/
import Mathlib

open MvPolynomial

noncomputable section

namespace TIE

@[simp] theorem fin_mk0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := by ext; rfl
@[simp] theorem fin_mk1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := by ext; rfl
@[simp] theorem fin_mk2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := by ext; rfl
@[simp] theorem fin_mk3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := by ext; rfl

/-- La signatura η = diag(−1, 1, 1, 1). -/
def eta : Fin 4 → ℝ := ![(-1 : ℝ), 1, 1, 1]

/-- El operador de derivada parcial ∂_μ sobre polinomios. -/
def d (μ : Fin 4) (f : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.pderiv μ f

/-- Conmutatividad de las derivadas parciales: ∂_i ∂_j = ∂_j ∂_i. -/
lemma pderiv_comm' (i j : Fin 4) (f : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f)
      = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
      simp only [MvPolynomial.pderiv_mul, map_add, hp]
      by_cases h1 : k = j
      · subst h1
        by_cases h2 : k = i
        · subst h2; simp
        · simp only [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne h2, map_zero,
            MvPolynomial.pderiv_one]
          ring
      · by_cases h2 : k = i
        · subst h2
          simp only [MvPolynomial.pderiv_X_of_ne h1, MvPolynomial.pderiv_X_self, map_zero,
            MvPolynomial.pderiv_one]
          ring
        · simp only [MvPolynomial.pderiv_X_of_ne h1, MvPolynomial.pderiv_X_of_ne h2, map_zero]
          ring

/-- La perturbación puro gauge: h_μν = ∂_μξ_ν + ∂_νξ_μ. -/
def hPure (ξ : Fin 4 → MvPolynomial (Fin 4) ℝ) (μ ν : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  d μ (ξ ν) + d ν (ξ μ)

/-- La traza η^{μν} h_μν. -/
def trPure (ξ : Fin 4 → MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ μ, C (eta μ) * hPure ξ μ μ

/-- El tensor de Ricci linealizado (índices subidos con η diagonal). -/
def ricci1 (ξ : Fin 4 → MvPolynomial (Fin 4) ℝ) (μ ν : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  C (1/2) * ( ∑ α, C (eta α) *
              ( d α (d μ (hPure ξ α ν)) + d α (d ν (hPure ξ α μ))
                + C (-1) * d α (d α (hPure ξ μ ν)) )
            + C (-1) * d μ (d ν (trPure ξ)) )

set_option maxHeartbeats 4000000

/-- **M6 — teorema clave**: el tensor de Ricci linealizado del modo puro gauge se
anula idénticamente, para toda ξ polinómica. Es el contenido matemático del
"pure gauge" de TT24. -/
theorem pure_gauge_ricci_zero (ξ : Fin 4 → MvPolynomial (Fin 4) ℝ) (μ ν : Fin 4) :
    ricci1 ξ μ ν = 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp only [ricci1, hPure, trPure, d, eta, Fin.sum_univ_four,
      Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Fin.reduceFinMk, Fin.zero_eta, fin_mk0, fin_mk1, fin_mk2, fin_mk3] <;>
    simp only [map_add, map_zero, map_neg, neg_zero, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_one, MvPolynomial.C_neg, MvPolynomial.C_1,
      MvPolynomial.C_0, pderiv_comm'] <;>
    ring

end TIE
