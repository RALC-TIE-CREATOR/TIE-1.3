/-
TIE — Encargo Toroidal ronda 2 (doc 57): P6 (Burnside 216->56) y P7 (chi/phi) por puntos fijos,
mas §4 (deduccion del selector). Vía barata: fixed-points + orbit-stabilizer por estado.
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT

/-! ### P6 — Burnside del modelo de 3 lazos (216 estados, acción de S₃) -/
/-- Estado: (a1,a2,a3) ∈ {x,y,z}³ y (L12,L13,L23) ∈ {0,1}³. -/
abbrev Est3 := Fin 3 × Fin 3 × Fin 3 × Fin 2 × Fin 2 × Fin 2
/-- A↔B (a1↔a2; L13↔L23). -/
def gAB (s : Est3) : Est3 := (s.2.1, s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.2, s.2.2.2.2.1)
/-- A↔C (a1↔a3; L12↔L23). -/
def gAC (s : Est3) : Est3 := (s.2.2.1, s.2.1, s.1, s.2.2.2.2.2, s.2.2.2.2.1, s.2.2.2.1)
/-- B↔C (a2↔a3; L12↔L13). -/
def gBC (s : Est3) : Est3 := (s.1, s.2.2.1, s.2.1, s.2.2.2.2.1, s.2.2.2.1, s.2.2.2.2.2)
/-- Ciclo A→B→C→A. -/
def gABC (s : Est3) : Est3 := (s.2.1, s.2.2.1, s.1, s.2.2.2.2.2, s.2.2.2.1, s.2.2.2.2.1)
/-- Ciclo inverso A→C→B→A. -/
def gACB (s : Est3) : Est3 := (s.2.2.1, s.1, s.2.1, s.2.2.2.2.1, s.2.2.2.2.2, s.2.2.2.1)
/-- nº de enlaces (invariante de la acción). -/
def nLinks (s : Est3) : ℕ := (s.2.2.2.1 : ℕ) + (s.2.2.2.2.1 : ℕ) + (s.2.2.2.2.2 : ℕ)
/-- nº de elementos que fijan a `s` (incluida la identidad). -/
def stabCount (s : Est3) : ℕ := (([gAB, gAC, gBC, gABC, gACB] : List (Est3 → Est3)).filter (fun σ => σ s = s)).length + 1
/-- **Certificado (P6)**: puntos fijos de los 6 elementos: `216 · 36×3 · 6×2`. -/
theorem p6_fijos :
    (Finset.univ.filter (fun s : Est3 => s = s)).card = 216 ∧
    (Finset.univ.filter (fun s : Est3 => gAB s = s)).card = 36 ∧
    (Finset.univ.filter (fun s : Est3 => gAC s = s)).card = 36 ∧
    (Finset.univ.filter (fun s : Est3 => gBC s = s)).card = 36 ∧
    (Finset.univ.filter (fun s : Est3 => gABC s = s)).card = 6 ∧
    (Finset.univ.filter (fun s : Est3 => gACB s = s)).card = 6 := by
  native_decide
/-- **Certificado (P6-a)**: Burnside `(216 + 3·36 + 2·6)/6 = 56` ⇒ **56 órbitas**. -/
theorem p6_burnside : 216 + 3 * 36 + 2 * 6 = 336 ∧ 336 = 56 * 6 := by
  norm_num
/-- **Certificado (P6-c)**: tamaños por orbit-stabilizer (`6/|Stab|`): 120 estados de órbita 6 (20 órbitas),
    90 de órbita 3 (30) y 6 de órbita 1 (6). -/
theorem p6_tamanos :
    (Finset.univ.filter (fun s : Est3 => 6 / stabCount s = 6)).card = 120 ∧
    (Finset.univ.filter (fun s : Est3 => 6 / stabCount s = 3)).card = 90 ∧
    (Finset.univ.filter (fun s : Est3 => 6 / stabCount s = 1)).card = 6 := by
  native_decide
/-- **Certificado (P6-b)**: Burnside refinado por nº de enlaces: k=0 (y 3): `(27+3·9+2·3)/6 = 10`;
    k=1 (y 2): `(81+3·9+2·0)/6 = 18`. -/
theorem p6_por_k :
    ((Finset.univ.filter (fun s : Est3 => nLinks s = 0)).card = 27) ∧
    ((Finset.univ.filter (fun s : Est3 => nLinks s = 1)).card = 81) ∧
    ((Finset.univ.filter (fun s : Est3 => nLinks s = 2)).card = 81) ∧
    ((Finset.univ.filter (fun s : Est3 => nLinks s = 3)).card = 27) ∧
    ((27 + 3 * 9 + 2 * 3) / 6 = 10) ∧ ((81 + 3 * 9 + 2 * 0) / 6 = 18) := by
  native_decide

/-! ### P7 — conteos χ y φ -/
/-- χ ∈ {±1}³ (0 = +1, 1 = −1). -/
abbrev Chi3 := Fin 2 × Fin 2 × Fin 2
def cAB (c : Chi3) : Chi3 := (c.2.1, c.1, c.2.2)
def cAC (c : Chi3) : Chi3 := (c.2.2, c.2.1, c.1)
def cBC (c : Chi3) : Chi3 := (c.1, c.2.2, c.2.1)
def cABC (c : Chi3) : Chi3 := (c.2.1, c.2.2, c.1)
def cACB (c : Chi3) : Chi3 := (c.2.2, c.1, c.2.1)
/-- nº de «−1». -/
def minusCount (c : Chi3) : ℕ := (c.1 : ℕ) + (c.2.1 : ℕ) + (c.2.2 : ℕ)
/-- **Certificado (P7-χ)**: fijos `8 · 4×3 · 2×2` ⇒ Burnside `24/6 = 4` clases; y los tamaños
    de clase por nº de «−1» (invariante): `[1,3,3,1]`. -/
theorem p7_chi :
    ((Finset.univ.filter (fun c : Chi3 => cAB c = c)).card = 4) ∧
    ((Finset.univ.filter (fun c : Chi3 => cABC c = c)).card = 2) ∧
    (8 + 3 * 4 + 2 * 2 = 24 ∧ 24 = 4 * 6) ∧
    ((Finset.univ.filter (fun c : Chi3 => minusCount c = 0)).card = 1) ∧
    ((Finset.univ.filter (fun c : Chi3 => minusCount c = 1)).card = 3) ∧
    ((Finset.univ.filter (fun c : Chi3 => minusCount c = 2)).card = 3) ∧
    ((Finset.univ.filter (fun c : Chi3 => minusCount c = 3)).card = 1) := by
  native_decide
/-- φ: multisets de 3 sobre {u,d,s} = ternas ordenadas. -/
abbrev Phi3 := {x : Fin 3 × Fin 3 × Fin 3 // x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}
/-- nº de coords = 2 ('s'). -/
def scount (x : Phi3) : ℕ :=
  (if x.val.1 = 2 then 1 else 0) + (if x.val.2.1 = 2 then 1 else 0) + (if x.val.2.2 = 2 then 1 else 0)
/-- **Certificado (P7-φ)**: 10 clases; por extrañeza `[4,3,2,1]`. -/
theorem p7_phi :
    Fintype.card Phi3 = 10 ∧
    (Finset.univ.filter (fun x : Phi3 => scount x = 0)).card = 4 ∧
    (Finset.univ.filter (fun x : Phi3 => scount x = 1)).card = 3 ∧
    (Finset.univ.filter (fun x : Phi3 => scount x = 2)).card = 2 ∧
    (Finset.univ.filter (fun x : Phi3 => scount x = 3)).card = 1 := by
  native_decide

/-! ### §4 — Deducción del selector (aritmética sobre los conteos P3) -/
theorem selector_deduccion :
    ((3 : ℕ) = 9 - 4 - 2) ∧ ((7 : ℕ) = 4 + 3) ∧ ((9 : ℕ) = 4 + 3 + 2) ∧
    ((12 : ℕ) = 3 * 2 + 2 * 3) := by
  norm_num
/-! ### P5 — Esqueletos de 3 celdas (parcial: V/E desde las listas del doc 57) -/
/-- LÍNEA·esquinas (16 nodos, 28 aristas). -/
def lineaEsq : List (Fin 16 × Fin 16) := [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(4,8),(5,7),(5,9),(6,7),(6,10),(7,11),(8,9),(8,10),(8,12),(9,11),(9,13),(10,11),(10,14),(11,15),(12,13),(12,14),(13,15),(14,15)]
/-- L·esquinas (16 nodos, 28 aristas). -/
def lEsq : List (Fin 16 × Fin 16) := [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(4,8),(5,7),(5,9),(6,7),(6,10),(6,12),(7,11),(7,13),(8,9),(8,10),(9,11),(10,11),(10,14),(11,15),(12,13),(12,14),(13,15),(14,15)]
/-- LÍNEA·poleas (19 nodos, 52 aristas). -/
def lineaPol : List (Fin 19 × Fin 19) := [(0,1),(0,2),(0,4),(0,16),(1,3),(1,5),(1,16),(2,3),(2,6),(2,16),(3,7),(3,16),(4,5),(4,6),(4,8),(4,16),(4,17),(5,7),(5,9),(5,16),(5,17),(6,7),(6,10),(6,16),(6,17),(7,11),(7,16),(7,17),(8,9),(8,10),(8,12),(8,17),(8,18),(9,11),(9,13),(9,17),(9,18),(10,11),(10,14),(10,17),(10,18),(11,15),(11,17),(11,18),(12,13),(12,14),(12,18),(13,15),(13,18),(14,15),(14,18),(15,18)]
/-- L·poleas (19 nodos, 52 aristas). -/
def lPol : List (Fin 19 × Fin 19) := [(0,1),(0,2),(0,4),(0,16),(1,3),(1,5),(1,16),(2,3),(2,6),(2,16),(3,7),(3,16),(4,5),(4,6),(4,8),(4,16),(4,17),(5,7),(5,9),(5,16),(5,17),(6,7),(6,10),(6,12),(6,16),(6,17),(6,18),(7,11),(7,13),(7,16),(7,17),(7,18),(8,9),(8,10),(8,17),(9,11),(9,17),(10,11),(10,14),(10,17),(10,18),(11,15),(11,17),(11,18),(12,13),(12,14),(12,18),(13,15),(13,18),(14,15),(14,18),(15,18)]
/-- **Certificado (P5, V/E)**: los 4 esqueletos: (16,28), (16,28), (19,52), (19,52). -/
theorem p5_VE :
    (Fintype.card (Fin 16) = 16 ∧ lineaEsq.length = 28 ∧ lEsq.length = 28) ∧
    (Fintype.card (Fin 19) = 19 ∧ lineaPol.length = 52 ∧ lPol.length = 52) := by
  decide
end TIE.TMT
