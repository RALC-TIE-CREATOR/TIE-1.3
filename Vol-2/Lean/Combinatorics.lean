/-
TIE M5 — Combinatoria fina de las 24 plaquetas de Γ₂₁ (cap. 4, TMT)
Las plaquetas cuadradas {esquina, punto medio, centro, punto medio}, sus clasificaciones
por pares de ejes (8/8/8) y kink/antikink (12/12), y el conteo de pares que comparten
arista (F₃).
Cada esquina tiene exactamente 3 puntos medios adyacentes → C(3,2) = 3 plaquetas por
esquina → 8·3 = 24 plaquetas.
-/
import Mathlib
import TieFormal.Graph21

namespace TIE

open Corner Midpoint CenterNode Node

/-- Una plaqueta: la esquina y sus dos puntos medios (el centro es común). -/
structure Plaquette where
  corner : Corner
  m1 : Midpoint
  m2 : Midpoint
deriving DecidableEq, Repr

/-- Las 24 plaquetas, enumeradas esquina por esquina (3 por esquina). -/
def allPlaquettes : List Plaquette :=
  [ ⟨c000, m01, m02⟩, ⟨c000, m01, m04⟩, ⟨c000, m02, m04⟩
  , ⟨c001, m01, m13⟩, ⟨c001, m01, m15⟩, ⟨c001, m13, m15⟩
  , ⟨c010, m02, m23⟩, ⟨c010, m02, m26⟩, ⟨c010, m23, m26⟩
  , ⟨c011, m13, m23⟩, ⟨c011, m13, m37⟩, ⟨c011, m23, m37⟩
  , ⟨c100, m04, m45⟩, ⟨c100, m04, m46⟩, ⟨c100, m45, m46⟩
  , ⟨c101, m15, m45⟩, ⟨c101, m15, m57⟩, ⟨c101, m45, m57⟩
  , ⟨c110, m26, m46⟩, ⟨c110, m26, m67⟩, ⟨c110, m46, m67⟩
  , ⟨c111, m37, m57⟩, ⟨c111, m37, m67⟩, ⟨c111, m57, m67⟩ ]

/-- El conteo: 24 plaquetas (8 esquinas × 3 pares). -/
theorem plaquette_count : allPlaquettes.length = 24 := by native_decide

/-- Las plaquetas son distintas. -/
theorem plaquettes_nodup : allPlaquettes.Nodup := by native_decide

/-! ## Clasificación por pares de ejes (8/8/8) -/

/-- El eje de cada punto medio (del Cuadro 2.4 del cap. 4). -/
def axisOf : Midpoint → Nat
  | m01 => 0  -- z
  | m02 => 1  -- y
  | m04 => 2  -- x
  | m13 => 1  -- y
  | m15 => 2  -- x
  | m23 => 0  -- z
  | m26 => 2  -- x
  | m37 => 2  -- x
  | m45 => 0  -- z
  | m46 => 1  -- y
  | m57 => 1  -- y
  | m67 => 0  -- z

/-- Toda plaqueta usa exactamente DOS ejes distintos (no mezcla 3, no repite 1). -/
theorem plaquette_two_axes :
    allPlaquettes.all (fun p => axisOf p.m1 != axisOf p.m2) = true := by native_decide

/-- La distribución por pares de ejes: 8 plaquetas por cada par {x,y},{x,z},{y,z}. -/
theorem axis_distribution :
    (allPlaquettes.filter (fun p => ({axisOf p.m1, axisOf p.m2} : Finset Nat) = {0,1})).length = 8 ∧
    (allPlaquettes.filter (fun p => ({axisOf p.m1, axisOf p.m2} : Finset Nat) = {0,2})).length = 8 ∧
    (allPlaquettes.filter (fun p => ({axisOf p.m1, axisOf p.m2} : Finset Nat) = {1,2})).length = 8 := by
  decide

/-! ## La partición kink/antikink (12/12) -/

/-- Los dos tetraedros: tetA = {c000, c011, c101, c110}, tetB = {c001, c010, c100, c111}. -/
def inTetA : Corner → Bool
  | c000 => true | c011 => true | c101 => true | c110 => true
  | _ => false

/-- La partición por tetraedro da 12 + 12. -/
theorem kink_antikink_distribution :
    (allPlaquettes.filter (fun p => inTetA p.corner)).length = 12 ∧
    (allPlaquettes.filter (fun p => !inTetA p.corner)).length = 12 := by
  decide

/-! ## El conteo de pares que comparten arista (F₃) -/

/-- Las aristas de una plaqueta: c–m1, m1–centro, centro–m2, m2–c. -/
def edgesOf (p : Plaquette) : Finset (Node × Node) :=
  { (corner p.corner, mid p.m1), (mid p.m1, ctr origin)
  , (mid p.m2, ctr origin), (mid p.m2, corner p.corner) }

/-- Un par ordenado comparte arista si son plaquetas distintas con intersección no vacía. -/
def shareEdge (pq : Plaquette × Plaquette) : Bool :=
  (pq.1 != pq.2) && (edgesOf pq.1 ∩ edgesOf pq.2).Nonempty

/-- Los pares ordenados que comparten arista. -/
def orderedShared : List (Plaquette × Plaquette) :=
  (allPlaquettes.product allPlaquettes).filter shareEdge

/-- El conteo ordenado: 144 = 2 × 72. -/
theorem F3_ordered : orderedShared.length = 144 := by native_decide

/-- El conteo de pares DISTINTOS que comparten arista (el valor F₃ de la justificación
    del capítulo 4): 72. -/
theorem F3_pairs : orderedShared.length / 2 = 72 := by native_decide

end TIE
