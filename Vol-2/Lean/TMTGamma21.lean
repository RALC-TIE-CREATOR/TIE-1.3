/-
TIE — Linea 5 (TMT-E1), modulo 17: GAMMA21 / enteros bariónicos (entregables E7, E10, E11).
Estructura del barion: 8 esquinas + 12 puntos medios + 1 centro; enteros 8,12,6,4.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **E10**: `Gamma21 = 8` esquinas + `12` puntos medios + `1` centro = `21` nodos. -/
theorem Gamma21_nodes : (8 + 12 + 1 : ℕ) = 21 := by norm_num
/-- **E10**: `36` aristas (`12` aristas del cubo partidas en 2 = 24, + `12` al centro). -/
theorem Gamma21_edges : (2 * 12 + 12 : ℕ) = 36 := by norm_num
/-- **E10**: `24` plaquetas (`6` caras x `4` sub-cuadros). -/
theorem Gamma21_plaquettes : (6 * 4 : ℕ) = 24 := by norm_num
/-- **E10**: las `24` plaquetas coinciden con `|S4| = 24`. -/
theorem Gamma21_plaq_eq_S4 : (6 * 4 : ℕ) = Nat.factorial 4 := by decide
/-- **E7/E10**: el multiplicador `6` es `|S3|` (permutación de los 3 lazos). -/
theorem E7_six_is_S3 : Nat.factorial 3 = 6 := by decide
/-- **E10/E11**: `a = 8 m_pi` con `m_pi = (7/17)·base` => `a = (56/17)·base`. -/
theorem E10_a_over_base : (8 : ℚ) * (7 / 17) = 56 / 17 := by norm_num
/-- **E10**: los enteros `8,12,6,4` son conteos de nodos/simetrías de `Gamma21`/tetraedro. -/
theorem E10_integers :
    ((8 : ℕ), (12 : ℕ), Nat.factorial 3, (4 : ℕ)) = (8, 12, 6, 4) := by
  decide
/-! ### P4 (encargo Toroidal 41): el grafo de Γ21 — cubo subdividido -/
/-- **Aristas de Γ21** (21 nodos: 0–7 esquinas, 8–19 puntos medios, 20 centro):
    24 esquina–medio + 12 medio–centro = 36. -/
def gamma21Edges : List (Fin 21 × Fin 21) :=
  [(0, 8), (1, 8), (0, 9), (2, 9), (0, 10), (4, 10), (1, 11), (3, 11), (1, 12), (5, 12),
   (2, 13), (3, 13), (2, 14), (6, 14), (3, 15), (7, 15), (4, 16), (5, 16), (4, 17), (6, 17),
   (5, 18), (7, 18), (6, 19), (7, 19),
   (8, 20), (9, 20), (10, 20), (11, 20), (12, 20), (13, 20), (14, 20), (15, 20), (16, 20), (17, 20), (18, 20), (19, 20)]
/-- Adyacencia de Γ21. -/
def gamma21Adj (a b : Fin 21) : Prop := (a, b) ∈ gamma21Edges ∨ (b, a) ∈ gamma21Edges
instance instDecidableGamma21Adj : DecidableRel gamma21Adj :=
  fun a b => inferInstanceAs (Decidable ((a, b) ∈ gamma21Edges ∨ (b, a) ∈ gamma21Edges))
/-- **Certificado (P4)**: Γ21 tiene `V=21`, `E=36`. -/
theorem gamma21_VE : (Fintype.card (Fin 21), gamma21Edges.length) = (21, 36) := by
  decide
/-- **Certificado (P4-ii)**: tamaños de las clases: esquinas `8`, medios `12`, centro `1`. -/
theorem gamma21_class_sizes :
    ((Finset.univ.filter (fun v : Fin 21 => v.val < 8)).card = 8) ∧
    ((Finset.univ.filter (fun v : Fin 21 => 8 ≤ v.val ∧ v.val < 20)).card = 12) ∧
    ((Finset.univ.filter (fun v : Fin 21 => v.val = 20)).card = 1) := by
  decide
/-- **Certificado (P4-ii, separación de clases)**: las esquinas solo tocan medios;
    los medios tocan 2 esquinas + 1 centro; el centro solo toca medios. -/
theorem gamma21_separacion :
    (∀ c : Fin 21, c.val < 8 →
      (Finset.univ.filter (fun w : Fin 21 => gamma21Adj c w)).card = 3 ∧
      (Finset.univ.filter (fun w : Fin 21 => gamma21Adj c w ∧ w.val < 8)).card = 0) ∧
    (∀ m : Fin 21, 8 ≤ m.val → m.val < 20 →
      (Finset.univ.filter (fun w : Fin 21 => gamma21Adj m w ∧ w.val < 8)).card = 2 ∧
      (Finset.univ.filter (fun w : Fin 21 => gamma21Adj m w ∧ w.val = 20)).card = 1) ∧
    (∀ w : Fin 21, gamma21Adj 20 w → 8 ≤ w.val ∧ w.val < 20) := by
  decide
/-- **Certificado (P4, maximalidad doc 42)**: el centro es el **ÚNICO** vértice de grado 12
    (⇒ todo automorfismo de Γ21 lo fija; con las clases separadas y el grupo del cubo
    (`cube_aut_card` = 48), queda respaldada la maximalidad de `|Aut| = 48`). -/
theorem gamma21_center_unique_deg12 :
    ((Finset.univ.filter (fun v : Fin 21 => (Finset.univ.filter (fun w : Fin 21 => gamma21Adj v w)).card = 12)).card = 1) ∧
    (∀ v : Fin 21, (Finset.univ.filter (fun w : Fin 21 => gamma21Adj v w)).card = 12 → v.val = 20) := by
  decide
end TIE.TMT
