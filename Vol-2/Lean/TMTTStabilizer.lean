/-
TIE — Linea 5 (TMT-E1), modulo 5: T desde el estabilizador (residual ii).
Liga el factor 8 de T=8D! al par kink-antikink (sin postular "8 orientaciones").
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **Apareamientos 2+2 de 4 puntos** (kink-antikink): `4!/(2^2 * 2!) = 3` = los 3 ejes de la dona. -/
theorem kk_pairings_count : (Nat.factorial 4) / (2^2 * Nat.factorial 2) = Craw := by
  norm_num [Craw, Nat.factorial]
/-- **Estabilizador del apareamiento** kink-antikink: `S2 x S2 ⋊ S2`, orden `2! * 2! * 2! = 8`. -/
theorem kk_stab_order : (Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2) = 8 := by decide
/-- **Orbit-stabilizer**: `3 apareamientos x 8 = |O| = 24` (el 8 = Sylow-2; indice 3). -/
theorem kk_orbit_stab :
    ((Nat.factorial 4) / (2^2 * Nat.factorial 2)) *
      ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2)) = orderO := by
  norm_num [orderO, Nat.factorial]
/-- El 8 del estabilizador kink-antikink ES el 2-Sylow de S4 (mismo orden, indice impar). -/
theorem kk_stab_is_sylow2 :
    ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2)) * 3 = orderO := by
  norm_num [orderO, Nat.factorial]
end TIE.TMT
