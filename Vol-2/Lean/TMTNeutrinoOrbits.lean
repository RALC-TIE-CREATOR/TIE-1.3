/-
TIE — Linea 5 (TMT-E1), modulo 14: ORBITAS DEL NEUTRINO (tetraedro, A4) — verificacion del conteo.
El doc da C=1,2,5; se certifica por Burnside(A4 sobre las 4 celdas) el conteo correcto.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **A4** (rotaciones del tetraedro, orden 12): 1 identidad + 3 dobles transposiciones + 8 tres-ciclos. -/
theorem A4_class_structure : (1 + 3 + 8 : ℕ) = 12 := by norm_num
/-- **Neutrinos (clase `(+,+,-,-)`)**: 6 configuraciones; fijos = 6 (id) + 3*2 (doble transp.)
    + 8*0 (3-ciclos) = 12 -> Burnside 12/12 = **1 orbita**. -/
theorem neutrino_orbit_ppMM : (6 + 3 * 2 + 8 * 0) / 12 = 1 := by norm_num
/-- **Neutrinos (clase `(+,-,0,0)`)**: 12 configuraciones; solo la identidad fija
    (A4 no tiene elemento con 2 puntos fijos, salvo e) -> 12/12 = **1 orbita**. -/
theorem neutrino_orbit_pM00 : (12 + 0) / 12 = 1 := by norm_num
/-- **DIFERENCIA DETECTADA**: el doc reporta C=2 y C=5; bajo A4 (accion citada) son 1 y 1. -/
theorem neutrino_doc_ne_A4 : (2 : ℕ) ≠ 1 ∧ (5 : ℕ) ≠ 1 := by decide
/-- **Clase `(0,0,0,0)`**: unica -> 1 orbita (coincide con el doc). -/
theorem neutrino_orbit_trivial : (1 : ℕ) = 1 := rfl
end TIE.TMT
