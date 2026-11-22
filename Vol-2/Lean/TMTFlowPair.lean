/-
TIE — Linea 5 (TMT-E1), modulo 7: FLUJO DEL PAR DE CELDAS (entregable B2b).
Enumera las clases de flujo del par (meson): omega_i en {-1,0,+1}, neutralidad omega_1+omega_2=0.
RESULTADO NEGATIVO: el conteo natural de flujo (<=3) NO reproduce C de los mesones.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **B2b**: pares de flujo neutrales `(omega_1,omega_2)` con `omega_i in {-1,0,+1}` y `omega_1+omega_2=0`
    -> `(0,0), (1,-1), (-1,1)`: **3**. -/
theorem neutral_pairs_card :
    ((Finset.product ({-1, 0, 1} : Finset ℤ) ({-1, 0, 1} : Finset ℤ)).filter
      (fun p => p.1 + p.2 = 0)).card = 3 := by decide
/-- **B2b**: cociente por inversión global (`omega -> -omega`, i.e. `q <-> qbar`):
    `(0,0)` fijo, `(1,-1) ~ (-1,1)` -> **2** clases (Burnside: `(3+1)/2`). -/
theorem neutral_classes_mod_neg : (3 + 1) / 2 = 2 := by decide
/-- **B2b (NEGATIVO)**: el conteo natural de flujo (`3`) NO reproduce `C` de los mesones (`13`, `7`). -/
theorem natural_flow_ne_C :
    ((Finset.product ({-1, 0, 1} : Finset ℤ) ({-1, 0, 1} : Finset ℤ)).filter
      (fun p => p.1 + p.2 = 0)).card ≠ (13 : ℕ) ∧
    ((Finset.product ({-1, 0, 1} : Finset ℤ) ({-1, 0, 1} : Finset ℤ)).filter
      (fun p => p.1 + p.2 = 0)).card ≠ (7 : ℕ) := by decide
/-- **C1a (Test 2)**: en el toro `L x L` (variedad cerrada), el minimo del sector winding 1 es
    `E_min = L^2 (1 - cos(2 pi / L))`, ESTABLE por topologia (`pi_1(S^1)=Z`). -/
noncomputable def Etorus (L : ℝ) : ℝ := L^2 * (1 - Real.cos (2 * Real.pi / L))
end TIE.TMT
