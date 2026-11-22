/-
TIE — Teoría Cuántica (Cap. 7, TMQ): paso TMQ1 (BARRIDO_TMQ_LEAN.md)

A07-01 (histórico): la factorización de Klein–Gordon **impresa** en el texto era
falsa (doble error de signo); el texto V1.3 ya trae la forma correcta. Con `D = iγ^μ∂_μ` y la relación de Clifford
(que da `D² = −□`), la identidad CORRECTA es

    (D + λ)(D − λ) = −(□ + λ²)      (λ = mc/ℏ),

y la versión impresa (`= □ − λ²`) solo se cumple si `□ = 0`.

Se certifican ambas, más la consecuencia Dirac⟹KG. Álgebra pura (`ring`).
El resto del capítulo es física/programa; ver el barrido (A07-02..A07-17).
-/
import Mathlib

noncomputable section

namespace TIE

/-- **TMQ1 (factorización KG corregida)**: con `D² = −□` (relación de Clifford),
    `(D+λ)(D−λ) = −(□+λ²)`. -/
theorem kg_factorization (D box lam : ℝ) (hD : D^2 = -box) :
    (D + lam) * (D - lam) = -(box + lam^2) := by
  rw [show (D + lam) * (D - lam) = D^2 - lam^2 by ring, hD]; ring

/-- **TMQ1 (la versión impresa es falsa salvo □=0)**: `(D+λ)(D−λ) = □−λ²`
    si y solo si `□ = 0`. -/
theorem kg_printed_iff (D box lam : ℝ) (hD : D^2 = -box) :
    ((D + lam) * (D - lam) = box - lam^2) ↔ box = 0 := by
  rw [show (D + lam) * (D - lam) = D^2 - lam^2 by ring, hD]
  constructor <;> intro h <;> linarith

/-- **TMQ1 (Dirac ⟹ Klein–Gordon)**: si `(D−λ)ψ = 0` y `D² = −□`, entonces
    `(□+λ²)ψ = 0`. -/
theorem dirac_implies_kg (D box lam psi : ℝ) (hD : D^2 = -box)
    (h : (D - lam) * psi = 0) :
    (box + lam^2) * psi = 0 := by
  calc (box + lam^2) * psi = -((D - lam) * (D + lam)) * psi := by ring_nf; rw [hD]; ring
    _ = -((D + lam) * ((D - lam) * psi)) := by ring
    _ = 0 := by rw [h]; ring

end TIE
