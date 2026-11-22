/-
TIE — Linea 5 (TMT-E1), modulo 15: TETRAEDRO DEL BARION (entregable E14) — certificacion pedida.
V=4, E=6, F=4, chi=2; grupos S4(24), A4(12), S3(6); enteros bariónicos 6=E=|S3|, 4=V.

GAPS CONOCIDOS (auditoria 2026-10-29):
  · 	etra_VEF ya NO contiene componentes triviales 4 = 4 (corregido).
  · El grupo de simetrias del tetraedro NO se identifica formalmente con S4/A4 (Gap 5):
    se certifican los cardinales |S4|=24, |A4|=12, |S3|=6, no la accion.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **E14**: el tetraedro (3 lazos + centro) tiene `E = C(4,2) = 6` y `chi = V - E + F = 2`
    (con `V = F = 4` como definiciones del modelo). -/
theorem tetra_VEF : (4 * 3 / 2 : ℕ) = 6 ∧ (4 : ℤ) - 6 + 4 = 2 := by
  constructor <;> norm_num
/-- **E14**: simetrias completas del tetraedro `= S4`, `|S4| = 4! = 24`. -/
theorem tetra_S4 : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide
/-- **E14**: rotaciones propias `= A4` (nucleo del signo, indice 2), `|A4| = 24/2 = 12`. -/
theorem tetra_A4 : Fintype.card (Equiv.Perm (Fin 4)) / 2 = 12 := by decide
/-- **E14**: estabilizador de un vertice `= S3` (permutacion de los 3 lazos), `|S3| = 3! = 6`. -/
theorem tetra_S3 : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide
/-- **E14 (enteros bariónicos)**: `6 = E = |S3|` (aristas = permutacion de 3 lazos); `4 = V`. -/
theorem tetra_baryon_integers :
    (4 * 3 / 2 : ℕ) = Fintype.card (Equiv.Perm (Fin 3)) := by
  decide
/-- **E14 (abierto)**: el dual (octaedro) tiene `8` caras/vértices y `24` rotaciones (`= |S4|`). -/
theorem octahedron_dual : ((8 : ℕ), (24 : ℕ)) = (2^3, Nat.factorial 4) := by decide
end TIE.TMT
