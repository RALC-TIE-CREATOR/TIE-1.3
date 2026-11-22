/-
TIE — Ticket T02 (Entrelazamiento): G2 — winding general de rutas en ℤ²\{0}.
(a) definición general (todas las direcciones, `Complex.arg` + desenrollado);
(b) CLASE mod 1: toda ruta de (−1,0) a (1,0) tiene W ≡ −1/2 (mod 1) (telescopado);
(c) invariancia bajo retrocesos.
-/
import Mathlib
import TieFormal.ENTLattice
namespace TIE.ENT
namespace P2
/-- Ángulo (rad) de un punto de la red — general, todas las direcciones. -/
noncomputable def angR (p : Pt) : ℝ := Complex.arg ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
lemma angR_one : angR (1, 0) = 0 := by
  simp [angR, Complex.arg_one]
lemma angR_neg_one : angR (-1, 0) = Real.pi := by
  simp [angR, Complex.arg_neg_one]
/-- Incremento angular desenrollado a (−π, π]. -/
noncomputable def dAng (a b : Pt) : ℝ :=
  let d := angR b - angR a
  if d > Real.pi then d - 2 * Real.pi else if d < -Real.pi then d + 2 * Real.pi else d
/-- El incremento angular es antisimétrico. -/
theorem dAng_antisymm (a b : Pt) : dAng a b = -dAng b a := by
  unfold dAng
  dsimp only
  split_ifs <;> linarith [Real.pi_pos]
/-- Cada incremento desenrollado difiere del crudo en un múltiplo entero de `2π`. -/
theorem dAng_mod (a b : Pt) : ∃ k : ℤ, dAng a b = (angR b - angR a) + k * (2 * Real.pi) := by
  unfold dAng
  dsimp only
  split_ifs with h1 h2
  · exact ⟨-1, by push_cast; ring⟩
  · exact ⟨1, by push_cast; ring⟩
  · exact ⟨0, by push_cast; ring⟩
/-- Suma cruda de diferencias angulares (sin desenrollar). -/
noncomputable def Sraw : List Pt → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (angR b - angR a) + Sraw (b :: rest)
/-- **(a)** Winding general en vueltas (desenrollado). -/
noncomputable def Wg : List Pt → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => dAng a b / (2 * Real.pi) + Wg (b :: rest)
/-- La suma cruda telescopa: solo dependen los extremos. -/
theorem Sraw_telescope (a : Pt) (mid : List Pt) (b : Pt) :
    Sraw (a :: mid ++ [b]) = angR b - angR a := by
  induction mid generalizing a with
  | nil =>
    have h1 : Sraw (a :: ([] : List Pt) ++ [b]) = (angR b - angR a) + Sraw [b] := rfl
    have h2 : Sraw [b] = 0 := rfl
    rw [h1, h2, add_zero]
  | cons c cs ih =>
    have hstep : Sraw (a :: (c :: cs) ++ [b]) = (angR c - angR a) + Sraw (c :: cs ++ [b]) := rfl
    rw [hstep, ih c]
    ring

/-- **(b)** La clase mod 1 del winding depende solo de los extremos. -/
theorem Wg_mod (a : Pt) (mid : List Pt) (b : Pt) :
    ∃ k : ℤ, Wg (a :: mid ++ [b]) = (angR b - angR a) / (2 * Real.pi) + k := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  induction mid generalizing a with
  | nil =>
    obtain ⟨k, hk⟩ := dAng_mod a b
    refine ⟨k, ?_⟩
    have hstep : Wg (a :: ([] : List Pt) ++ [b]) = dAng a b / (2 * Real.pi) + Wg [b] := rfl
    have hzero : Wg [b] = 0 := rfl
    rw [hstep, hzero, hk]
    push_cast
    field_simp
    ring
  | cons c cs ih =>
    obtain ⟨k, hk⟩ := dAng_mod a c
    obtain ⟨k2, h2⟩ := ih c
    refine ⟨k + k2, ?_⟩
    have hstep : Wg (a :: (c :: cs) ++ [b]) = dAng a c / (2 * Real.pi) + Wg (c :: cs ++ [b]) := rfl
    rw [hstep, hk, h2]
    push_cast
    field_simp
    ring
/-- **(b)** Toda ruta de `(−1,0)` a `(1,0)` tiene winding `≡ −1/2 (mod 1)`. -/
theorem exchange_class (mid : List Pt) :
    ∃ k : ℤ, Wg ((-1, 0) :: mid ++ [(1, 0)]) = -(1/2) + k := by
  obtain ⟨k, hk⟩ := Wg_mod (-1, 0) mid (1, 0)
  refine ⟨k, ?_⟩
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [hk, angR_neg_one, angR_one]
  push_cast
  field_simp
  ring
/-- **(c)** Invariancia del winding bajo inserción/borrado de un retroceso. -/
theorem Wg_backtrack (p q : Pt) (rest : List Pt) :
    Wg (p :: q :: p :: rest) = Wg (p :: rest) := by
  cases rest with
  | nil =>
    have h1 : Wg (p :: q :: p :: ([] : List Pt)) = dAng p q / (2 * Real.pi) + Wg (q :: p :: []) := rfl
    have h2 : Wg (q :: p :: ([] : List Pt)) = dAng q p / (2 * Real.pi) + Wg [p] := rfl
    have h3 : Wg [p] = 0 := rfl
    rw [h1, h2, h3, dAng_antisymm p q]
    ring
  | cons r rs =>
    have h1 : Wg (p :: q :: p :: r :: rs) = dAng p q / (2 * Real.pi) + Wg (q :: p :: r :: rs) := rfl
    have h2 : Wg (q :: p :: r :: rs) = dAng q p / (2 * Real.pi) + Wg (p :: r :: rs) := rfl
    have h3 : Wg (p :: r :: rs) = dAng p r / (2 * Real.pi) + Wg (r :: rs) := rfl
    rw [h1, h2, h3, dAng_antisymm p q]
    ring
/-- **(c)** La clase mod 1 es invariante bajo CUALQUIER deformación con extremos fijos. -/
theorem Wg_class_eq (a b : Pt) (m1 m2 : List Pt) :
    ∃ k : ℤ, Wg (a :: m1 ++ [b]) = Wg (a :: m2 ++ [b]) + k := by
  obtain ⟨k1, h1⟩ := Wg_mod a m1 b
  obtain ⟨k2, h2⟩ := Wg_mod a m2 b
  exact ⟨k1 - k2, by rw [h1, h2]; push_cast; ring⟩
/-- **TMT · «el lazo plano es imposible para fermiones»**: el winding del lazo de intercambio
    nunca es 0, así que la ruta no es contráctil (no puede aplanarse a la identidad).
    Se sigue de `exchange_class` (`W = −1/2 + k`) y de la integralidad de `k`.
    Gap declarado (Gap 5): núcleo topológico‑combinatorio; la identificación con el spin‑½
    (premisa de modelado) no se formaliza aquí. -/
theorem exchange_winding_ne_zero (mid : List Pt) :
    Wg ((-1, 0) :: mid ++ [(1, 0)]) ≠ 0 := by
  obtain ⟨k, hk⟩ := exchange_class mid
  intro h0
  have hk0 : (-(1 / 2 : ℝ) + (k : ℝ)) = 0 := by
    rw [← hk]
    exact h0
  have h2 : (k : ℝ) = 1 / 2 := by linarith
  have h3 : ((2 * k : ℤ) : ℝ) = 1 := by
    push_cast
    linarith
  have h4 : (2 * k : ℤ) = 1 := by exact_mod_cast h3
  omega
end P2
end TIE.ENT
