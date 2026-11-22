/-
TIE — Cierre del gap `O ≅ S4` (auditoría 2026-10-30).
Formaliza el grupo de ROTACIONES del cubo como subconjunto explícito de `Perm (Fin 8)` y
DERIVA de la acción: |O| = 24, la tabla de orbit-stabilizer (8/3, 12/2, 3/8, 4/6) y la
fidelidad de la acción sobre las 4 diagonales (⇒ O ≅ S4).

Rotaciones = automorfismos del cubo con signo de orientación +1 (determinante de la
transformación inducida sobre los ejes). Un test LOCAL de orientación (sólo la terna en el
vértice imagen de 0) selecciona A4 x C2, no las rotaciones: por eso se usa el determinante.

NOTA DE ESTÁNDAR: certificados con `native_decide` (el kernel `decide` excede la profundidad de
recursión al enumerar `Perm (Fin 8)`, 40320 elementos). Etiquetar como «native-decide».
-/
import Mathlib
import TieFormal.TMTGraph
namespace TIE.TMT
/-- ¿Es `σ` un automorfismo del grafo del cubo? -/
def cubeAut (σ : Equiv.Perm (Fin 8)) : Bool :=
  decide (∀ u v : Fin 8, cubeEdge u v ↔ cubeEdge (σ u) (σ v))
/-- Signo de la dirección del eje `m` visto desde `w` (hacia fuera = +1). -/
def dirSign (w : Fin 8) (m : ℕ) : ℤ := if w.val &&& m = 0 then 1 else -1
/-- Eje (0,1,2) de una máscara de un bit. -/
def axisOfMask (m : ℕ) : Fin 3 := if m = 1 then 0 else if m = 2 then 1 else 2
/-- Signo de una terna de índices de eje. -/
def sign3 (a b c : Fin 3) : ℤ :=
  if a = 0 then (if b = 1 then 1 else -1)
  else if a = 1 then (if b = 0 then -1 else 1)
  else (if b = 0 then 1 else -1)
/-- **Signo de orientación** de `σ`: determinante de la transformación inducida sobre los ejes
    (permutación de ejes × signos de dirección desde el vértice imagen de 0). -/
def orientSign (σ : Equiv.Perm (Fin 8)) : ℤ :=
  let w := σ 0
  let m1 := (σ ⟨1, by decide⟩).val ^^^ w.val
  let m2 := (σ ⟨2, by decide⟩).val ^^^ w.val
  let m3 := (σ ⟨4, by decide⟩).val ^^^ w.val
  sign3 (axisOfMask m1) (axisOfMask m2) (axisOfMask m3) * dirSign w m1 * dirSign w m2 * dirSign w m3
/-- ¿Es `σ` una ROTACIÓN? = automorfismo con determinante +1. -/
def isRot (σ : Equiv.Perm (Fin 8)) : Bool :=
  cubeAut σ && (orientSign σ == 1)
/-- **El grupo de rotaciones del cubo**, como subconjunto de `Perm (Fin 8)`. -/
def Oset : Finset (Equiv.Perm (Fin 8)) := Finset.univ.filter (fun σ => isRot σ)
/-- **`O_card_rot`**: el grupo de rotaciones tiene **24** elementos. -/
theorem O_card_rot : Oset.card = 24 := by native_decide
/-- La identidad es una rotación. -/
theorem Oset_one : (1 : Equiv.Perm (Fin 8)) ∈ Oset := by native_decide
/-- `Oset` es cerrado bajo composición. -/
theorem Oset_mul : ∀ σ : {σ // σ ∈ Oset}, ∀ τ : {τ // τ ∈ Oset}, (σ.1 * τ.1) ∈ Oset := by
  native_decide
/-- `Oset` es cerrado bajo inversa. -/
theorem Oset_inv : ∀ σ : {σ // σ ∈ Oset}, σ.1⁻¹ ∈ Oset := by native_decide
/-- **Chequeo de auditoría**: la inversión central (`v ↦ v⊕7`) **NO** es una rotación. -/
theorem inversion_not_rot :
    (Oset.filter (fun σ => ∀ i : Fin 8, (σ i).val = i.val ^^^ 7)).card = 0 := by native_decide
/-- **Esquinas**: órbita 8, estabilizador 3 (derivados de la acción). -/
theorem orbit_vertex : (Oset.image (fun σ => σ 0)).card = 8 := by native_decide
theorem stab_vertex : (Oset.filter (fun σ => σ 0 = 0)).card = 3 := by native_decide
/-- **Aristas**: órbita 12, estabilizador 2. -/
theorem orbit_edge : (Oset.image (fun σ => ({σ 0, σ ⟨1, by decide⟩} : Finset (Fin 8)))).card = 12 := by
  native_decide
theorem stab_edge :
    (Oset.filter (fun σ => ({σ 0, σ ⟨1, by decide⟩} : Finset (Fin 8)) = {0, 1})).card = 2 := by
  native_decide
/-- **Ejes** (par de caras opuestas): órbita 3, estabilizador 8. -/
theorem orbit_axis :
    (Oset.image (fun σ => ({Finset.image (fun x => σ x) ({0, 1, 2, 3} : Finset (Fin 8)),
                            Finset.image (fun x => σ x) ({4, 5, 6, 7} : Finset (Fin 8))}
                          : Finset (Finset (Fin 8))))).card = 3 := by
  native_decide
theorem stab_axis :
    (Oset.filter (fun σ => ({Finset.image (fun x => σ x) ({0, 1, 2, 3} : Finset (Fin 8)),
                             Finset.image (fun x => σ x) ({4, 5, 6, 7} : Finset (Fin 8))}
                           : Finset (Finset (Fin 8)))
      = ({({0, 1, 2, 3} : Finset (Fin 8)), ({4, 5, 6, 7} : Finset (Fin 8))}
          : Finset (Finset (Fin 8))))).card = 8 := by
  native_decide
/-- **Diagonales del cuerpo**: órbita 4, estabilizador 6. -/
theorem orbit_diag : (Oset.image (fun σ => ({σ 0, σ ⟨7, by decide⟩} : Finset (Fin 8)))).card = 4 := by
  native_decide
theorem stab_diag :
    (Oset.filter (fun σ => ({σ 0, σ ⟨7, by decide⟩} : Finset (Fin 8)) = {0, 7})).card = 6 := by
  native_decide
/-- Índice canónico de la diagonal que pasa por `v` (pares antipodales 0↔7, 1↔6, 2↔5, 3↔4). -/
def diagIdx (v : Fin 8) : Fin 4 :=
  if v.val = 0 then 0 else if v.val = 1 then 1 else if v.val = 2 then 2
  else if v.val = 3 then 3 else if v.val = 4 then 3 else if v.val = 5 then 2
  else if v.val = 6 then 1 else 0
/-- **`|S4| = 24`** (cardinal de `Perm (Fin 4)`): junto con `O_card_rot`, fija el orden del iso. -/
theorem s4_card : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide
/-- **Fidelidad de la acción sobre las 4 diagonales**: dos rotaciones que inducen la MISMA
    permutación de las diagonales (evaluada en los representantes 0,1,2,3) coinciden.
    Con `O_card_rot` (24) y `s4_card` (24) esto da el isomorfismo `O ≅ S4`. -/
theorem diag_faithful :
    ∀ σ : {σ // σ ∈ Oset}, ∀ τ : {τ // τ ∈ Oset},
      (∀ d : Fin 4, diagIdx (σ.1 ⟨d.val, by have := d.isLt; omega⟩)
        = diagIdx (τ.1 ⟨d.val, by have := d.isLt; omega⟩)) → σ = τ := by
  native_decide
end TIE.TMT
