/-
TIE — Ticket ENT T01 (Entrelazamiento): P2 — lazo de intercambio en la red ℤ².
(a) ruta de intercambio sin colisión (4 ticks, un enlace por tick);
(b) invariante de lazo (winding) del vector relativo r = x₁ − x₂.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.ENT
namespace P2
/-- Punto de la red ℤ². -/
abbrev Pt := ℤ × ℤ
/-- Adyacencia Manhattan 1 en ℤ². -/
def adj (a b : Pt) : Prop := (a.1 - b.1).natAbs + (a.2 - b.2).natAbs = 1
/-- Tick: exactamente una ficha avanza 1 enlace; sin colisión. -/
def Tick (c c' : Pt × Pt) : Prop :=
  (adj c.1 c'.1 ∧ c'.2 = c.2 ∧ c'.1 ≠ c'.2) ∨ (adj c.2 c'.2 ∧ c'.1 = c.1 ∧ c'.1 ≠ c'.2)
def c0 : Pt × Pt := ((0, 0), (1, 0))
def c1 : Pt × Pt := ((0, 1), (1, 0))
def c2 : Pt × Pt := ((0, 1), (0, 0))
def c3 : Pt × Pt := ((1, 1), (0, 0))
def c4 : Pt × Pt := ((1, 0), (0, 0))
/-- **(a)** La ruta de intercambio: 4 ticks legales (mínima en ℤ²). -/
theorem exchange_ticks : Tick c0 c1 ∧ Tick c1 c2 ∧ Tick c2 c3 ∧ Tick c3 c4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Tick, adj, c0, c1, c2, c3, c4] <;> decide
/-- El intercambio termina con las fichas permutadas. -/
theorem exchange_swaps : c4 = (c0.2, c0.1) := by decide
/-- Vector relativo `r = x₁ − x₂`. -/
def rel (c : Pt × Pt) : Pt := (c.1.1 - c.2.1, c.1.2 - c.2.2)
/-- La ruta relativa del intercambio. -/
theorem rel_path :
    rel c0 = (-1, 0) ∧ rel c1 = (-1, 1) ∧ rel c2 = (0, 1) ∧
      rel c3 = (1, 1) ∧ rel c4 = (1, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [rel, c0, c1, c2, c3, c4] <;> decide
/-- Ángulo en unidades de π (exacto, ℚ). -/
def angQ (p : Pt) : ℚ :=
  if p = (-1, 0) then 1
  else if p = (-1, 1) then 3/4
  else if p = (0, 1) then 1/2
  else if p = (1, 1) then 1/4
  else if p = (1, 0) then 0
  else if p = (1, -1) then -(1/4)
  else if p = (0, -1) then -(1/2)
  else 0
/-- Incremento angular desenrollado (rama principal en (−1,1]). -/
def dstep (a b : ℚ) : ℚ :=
  let d := b - a
  if d > 1 then d - 2 else if d < -1 then d + 2 else d
/-- **(b)** Winding en vueltas con desenrollado: `W = (Σ Δθ/π)/2` ≡ `(ΣΔθ)/(2π)`. -/
def W (rs : List Pt) : ℚ :=
  ((rs.zip rs.tail).map (fun p => dstep (angQ p.1) (angQ p.2))).sum / 2
/-- **(b)** Intercambio simple = media vuelta: `W = −1/2`. -/
theorem W_single : W [(-1,0), (-1,1), (0,1), (1,1), (1,0)] = -(1/2) := by native_decide
/-- **(b)** Doble intercambio (mismo sentido) = vuelta completa: `W = −1`. -/
theorem W_double :
    W [(-1,0), (-1,1), (0,1), (1,1), (1,0), (1,-1), (0,-1), (-1,0)] = -1 := by native_decide
end P2
end TIE.ENT