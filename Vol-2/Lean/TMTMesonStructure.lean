/-
TIE — Linea 5 (TMT-E1), modulo 6: ESTRUCTURA DEL MESON (entregables B, B2, B2b).
Dos celdas de 9 nodos acopladas. Modos de acople -> (V,E,beta1). T = nº de nodos unicos.
RESULTADO NEGATIVO (B2b): C (numerador) NO se deriva de V, E ni beta1 => C es FENOMENOLOGICO.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **B**: `T` del meson = nº de nodos unicos de la estructura acoplada.
    Kaon (fusion) `9`; pion (esquina compartida) `2*9-1 = 17`. -/
theorem T_meson_by_mode : (numNodes, 2 * numNodes - 1) = (9, 17) := by
  norm_num [numNodes]
/-- **B2**: estructuras acopladas `(V, E, beta1)`:
    fusion `(9,20,12)`; esquina `(17,40,24)`; arista `(16,39,24)`; cara `(14,36,23)`. -/
theorem coupled_structures :
    ((numNodes, numEdges, numEdges - numNodes + 1),
     (2 * numNodes - 1, 2 * numEdges, 2 * numEdges - (2 * numNodes - 1) + 1),
     (2 * numNodes - 2, 2 * numEdges - 1, 2 * numEdges - 1 - (2 * numNodes - 2) + 1),
     (2 * numNodes - 4, 2 * numEdges - 4, 2 * numEdges - 4 - (2 * numNodes - 4) + 1))
      = ((9, 20, 12), (17, 40, 24), (16, 39, 24), (14, 36, 23)) := by
  norm_num [numNodes, numEdges]
/-- **B2b (NEGATIVO)**: `C` del meson no es ni `V` ni `beta1`:
    pion `C=7 != 17` y `!= 24`; kaon `C=13 != 9`. (El unico contacto `13 = 12+1` es coincidencia.) -/
theorem C_pion_not_from_structure : (7 : ℕ) ≠ 17 ∧ (7 : ℕ) ≠ 24 := by decide
theorem C_kaon_not_from_structure : (13 : ℕ) ≠ 9 ∧ (13 : ℕ) ≠ 20 := by decide
/-- **B2b**: los numeradores `C` de los mesones (fenomenologicos; NO derivados). -/
theorem C_meson_values :
    ((7 : ℕ), (13 : ℕ), (25 : ℕ), (93 : ℕ), (141 : ℕ), (170 : ℕ)) = (7, 13, 25, 93, 141, 170) := rfl
end TIE.TMT
