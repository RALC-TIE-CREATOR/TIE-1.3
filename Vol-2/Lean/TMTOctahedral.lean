/-
TIE — Linea 5 (TMT-E1), modulo 2: accion del grupo octaedrico O (S4) sobre el cubo.
Certifica orbit-stabilizer para cada tipo de elemento y el subgrupo de orden 8 (Sylow-2).

GAPS CONOCIDOS (auditoria 2026-10-29):
  · Aqui se certifican los PRODUCTOS de orbit-stabilizer (8*3 = 12*2 = 3*8 = 4*6 = 24),
    NO la accion de O sobre el cubo. El isomorfismo O ~ S4 y los tamanos de orbita se
    ASUMEN (Gap 4 estructural). Trabajo pendiente: formalizar O <= Perm (Fin 8) y derivarlos.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **TMT-02b (orbit-stabilizer)**: para cada tipo de elemento del cubo, |orbita| * |Stab| = |O| = 24. -/
theorem orbit_stab_corners   : 8 * 3 = orderO := by norm_num [orderO]
theorem orbit_stab_edges     : 12 * 2 = orderO := by norm_num [orderO]
theorem orbit_stab_axes      : 3 * 8 = orderO := by norm_num [orderO]
theorem orbit_stab_diagonals : 4 * 6 = orderO := by norm_num [orderO]
/-- **TMT-02b (H2)**: el estabilizador de un eje (o el subgrupo que fija la clase kink-antikink)
    tiene orden `8 = |O|/3`, y `8` es la mayor potencia de 2 que divide `24` (indice `3` impar)
    => es un subgrupo de Sylow-2 de `O ≅ S4` (isomorfo a `D4`). -/
theorem stab_axis_order : orderO / 3 = 8 := by norm_num [orderO]
theorem sylow2_index_odd : 8 * 3 = orderO ∧ ¬ (2 ∣ 3) := by
  constructor <;> · norm_num [orderO]
/-- **TMT-03b**: `C=3` (threadings etiquetados) coincide numericamente con el tamano de la
    orbita de los 3 ejes bajo `O`; el estabilizador de un eje (`|Stab|=8`) da `T`-like degeneracion. -/
theorem axes_orbit_and_stab : Craw = 3 ∧ orderO / 8 = 3 := by
  constructor <;> · norm_num [Craw, orderO]
end TIE.TMT
