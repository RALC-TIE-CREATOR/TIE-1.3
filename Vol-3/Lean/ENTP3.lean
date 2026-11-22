/-
TIE — Ticket ENT T01 (Entrelazamiento): P3 — puente condicional.
La premisa de modelado (el ciclo de interrogación CHSH ≡ el lazo de intercambio) es del autor;
aquí se certifica la parte matemática: el emparejamiento del carácter Z2 (−1 en la vuelta completa).
-/
import Mathlib
import TieFormal.ENTPauli
import TieFormal.ENTLattice
namespace TIE.ENT
namespace P3
/-- La premisa de modelado del puente CHSH (declarada, no derivada). -/
structure ModelPremise where
  /-- El ciclo de interrogación de un evento CHSH es el lazo de intercambio. -/
  ciclo_es_intercambio : Prop
  hpremisa : ciclo_es_intercambio
/-- Carácter Z₂: la vuelta completa (W = ±1) pesa −1. -/
def chi (w : ℚ) : ℤ := if w = 1 ∨ w = -1 then -1 else 1
theorem chi_completa : chi 1 = -1 ∧ chi (-1) = -1 := by
  constructor <;> simp [chi]
theorem chi_trivial : chi 0 = 1 := by simp [chi]
/-- **P3 (puente condicional)** — certificado el emparejamiento matemático bajo la premisa:
la vuelta completa de la red (doble intercambio, `W = −1`) y la rotación de 2π del espinor
(`R(2π) = exp(iπσ₃) = −I`, con `J = σ/2`) comparten el carácter `−1`. -/
theorem puente (m : ModelPremise) :
    m.ciclo_es_intercambio ∧
    (P2.W [(-1,0), (-1,1), (0,1), (1,1), (1,0), (1,-1), (0,-1), (-1,0)] = -1) ∧
    (NormedSpace.exp ((Real.pi * Complex.I) • s3) = -(1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (chi (P2.W [(-1,0), (-1,1), (0,1), (1,1), (1,0), (1,-1), (0,-1), (-1,0)]) = -1) := by
  exact ⟨m.hpremisa, P2.W_double, exp_pi_s3, by rw [P2.W_double]; simp [chi]⟩
end P3
end TIE.ENT
