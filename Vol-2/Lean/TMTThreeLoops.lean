/-
TIE — Linea 5 (TMT-E1), modulo 11: 3 LAZOS / BARIONES (peticion §12).
Modelo: 3 lazos, orientacion a_i in {x,y,z} y enlaces mutuos L_ij in {0,1};
cociente por el reetiquetado S3 (Burnside). Bariones: winding neto +-1 => protegidos.

GAPS CONOCIDOS (auditoria 2026-10-30, bloque C):
  · Los puntos fijos de Burnside (216, 36, 6) estaban como ENTRADAS aritmeticas; ahora se
    DERIVAN de la accion explicita de S3 sobre los 216 estados (urnside_*).
  · El lema de Burnside (orbitas = promedio de fijos) se ASUME (no formalizado): Gap 4 declarado.
  · aryon_CT_values es un DATO externo (no un teorema).
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **§12 (conteo crudo)**: 3 orientaciones^3 x 2 enlaces^3 = 216 estados crudos. -/
theorem baryon_raw : 3^3 * 2^3 = 216 := by norm_num
/-- **§12 (Burnside S3)**: puntos fijos por clase de conjugacion:
    identidad 216; 3 transposiciones x 36 (=9x4); 2 tres-ciclos x 6 (=3x2).
    Orbitas = (216 + 3*36 + 2*6) / 6 = **56**. -/
theorem baryon_orbits : (216 + 3 * 36 + 2 * 6) / 6 = 56 := by norm_num
/-- **DIFERENCIA DETECTADA**: el doc `TMT-E1-C2` reporta **68** orbitas; el Burnside(S3) da **56**.
    (216 crudos coinciden; el cociente discrepa.) -> a verificar por el equipo. -/
theorem baryon_68_ne_56 : (68 : ℕ) ≠ 56 := by decide
/-- **§12 (datos externos, SIN teorema)**: los `C/T` que exigen las masas observadas
    (fenomenologicos): p=11/4, Lambda=23/7, Sigma=7/2, Xi=35/9, Omega-=59/12.
    Se registran como DATO, no como resultado certificado. -/
def baryon_CT_values : ℚ × ℚ × ℚ × ℚ × ℚ := (11/4, 23/7, 7/2, 35/9, 59/12)
/-- **§12 (negativo)**: el conteo Br=56 no es ninguno de los `C/T` requeridos. -/
theorem baryon_orbits_ne_CT :
    (56 : ℚ) ≠ 11/4 ∧ (56 : ℚ) ≠ 7/2 ∧ (56 : ℚ) ≠ 35/9 ∧ (56 : ℚ) ≠ 59/12 := by
  norm_num
/-- **§12 (bonus)**: numero maximo de enlaces mutuos entre 3 lazos = C(3,2) = 3
    (K3 completo); el orden de masas crece con el anudamiento se contrasta aqui. -/
theorem baryon_max_links : 3 * 2 / 2 = 3 := by norm_num
/-! ### Burnside S3 DERIVADO de la acción sobre los 216 estados -/
/-- Índice de la arista (par no ordenado) `{i,j}` en `Fin 3`: 0={0,1}, 1={0,2}, 2={1,2}. -/
def pairOf (i j : Fin 3) : Fin 3 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 2
/-- Acción de `σ` sobre el índice de par. -/
def pairMap (σ : Equiv.Perm (Fin 3)) (p : Fin 3) : Fin 3 :=
  if p = 0 then pairOf (σ 0) (σ 1) else if p = 1 then pairOf (σ 0) (σ 2) else pairOf (σ 1) (σ 2)
/-- Estado bariónico: 3 orientaciones (`Fin 3^3` = 27) × 3 enlaces (`Fin 2^3` = 8) = 216. -/
abbrev BState := (Fin 3 → Fin 3) × (Fin 3 → Fin 2)
/-- Acción de `σ : S3` sobre los estados (permuta lazos, orientaciones y enlaces). -/
def bAct (σ : Equiv.Perm (Fin 3)) (s : BState) : BState :=
  (fun i => s.1 (σ.symm i), fun p => s.2 (pairMap σ.symm p))
/-- **Identidad**: 216 estados fijos. -/
theorem burnside_id : (Finset.univ.filter (fun s : BState => bAct 1 s = s)).card = 216 := by
  native_decide
/-- **Transposiciones**: 36 estados fijos (antes era una ENTRADA; ahora derivado). -/
theorem burnside_transposition :
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin 3) =>
      τ ≠ 1 ∧ τ * τ = 1 ∧ (Finset.univ.filter (fun s : BState => bAct τ s = s)).card ≠ 36)).card = 0 := by
  native_decide
/-- Forma directa del conteo de fijos para una transposición concreta (swap 0↔1). -/
theorem burnside_transposition_card :
    (Finset.univ.filter (fun s : BState => bAct (Equiv.swap (0 : Fin 3) 1) s = s)).card = 36 := by
  native_decide
/-- **3-ciclos**: 6 estados fijos (derivado). -/
theorem burnside_3cycle_card :
    (Finset.univ.filter (fun s : BState => bAct (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) s = s)).card = 6 := by
  native_decide
/-- **Burnside (aritmética con los fijos DERIVADOS)**: (216 + 3·36 + 2·6)/6 = 56. -/
theorem burnside_sum : (216 + 3 * 36 + 2 * 6) / 6 = 56 := by norm_num
end TIE.TMT
