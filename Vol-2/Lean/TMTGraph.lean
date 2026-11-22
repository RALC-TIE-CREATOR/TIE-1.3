/-
TIE — Tema GRAFO (2): la celda como `SimpleGraph` real + hechos certificados.
8 esquinas (0..7) + centro (8); 20 aristas (12 del cubo + 8 al centro).
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- Aristas de la celda: 8 esquinas (0..7) + centro (8); 20 aristas. -/
def cellEdgeList : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6),
   (5, 7), (6, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7)]
/-- Adyacencia (no dirigida) de la celda. -/
def cellAdj (a b : Fin 9) : Prop := (a, b) ∈ cellEdgeList ∨ (b, a) ∈ cellEdgeList
/-- Simetría de la adyacencia. -/
theorem cellAdj_symm : ∀ a b : Fin 9, cellAdj a b → cellAdj b a := by
  intro a b h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
/-- La adyacencia es irreflexiva (sin lazos). -/
theorem cellAdj_irrefl : ∀ a : Fin 9, ¬ cellAdj a a := by
  intro a h
  rcases h with h | h <;> exact absurd h (by fin_cases a <;> decide)
/-- **Grafo de la celda** (`SimpleGraph`): 8 esquinas + centro. -/
abbrev cellGraph : SimpleGraph (Fin 9) where
  Adj := cellAdj
  symm := Std.Symm.mk cellAdj_symm
  loopless := Std.Irrefl.mk cellAdj_irrefl
/-- **Certificado**: 20 aristas. -/
theorem cellGraph_edges : cellEdgeList.length = 20 := rfl
/-- **Certificado**: 9 vértices. -/
theorem cellGraph_verts : Fintype.card (Fin 9) = numNodes := by simp [numNodes]
/-- **Certificado (Adyacencia)**: el centro `8` es adyacente a la esquina `0`. -/
theorem cellGraph_adj_center : cellGraph.Adj (8 : Fin 9) (0 : Fin 9) := by
  change cellAdj 8 0
  exact Or.inl (by decide)
/-- **Certificado (Sin lazos)**: el centro no es adyacente a sí mismo. -/
theorem cellGraph_noLoop : ¬ cellGraph.Adj (8 : Fin 9) (8 : Fin 9) := by
  change ¬ cellAdj 8 8
  exact cellAdj_irrefl 8
/-- **Certificado (Simetría)**: si `a` es adyacente a `b`, `b` lo es a `a`. -/
theorem cellGraph_symm (a b : Fin 9) : cellGraph.Adj a b → cellGraph.Adj b a :=
  cellAdj_symm a b
/-- **Certificado (Conectividad)**: todo vértice alcanza el centro `8`. -/
theorem cellGraph_reachable_center (a : Fin 9) : cellGraph.Reachable a 8 := by
  have h : a = 8 ∨ cellAdj a 8 := by
    fin_cases a <;> (first | exact Or.inl rfl | exact Or.inr (Or.inr (by decide)))
  rcases h with h | h
  · subst h; exact SimpleGraph.Reachable.refl 8
  · exact SimpleGraph.Adj.reachable h
/-- **Certificado (Conectividad)**: el centro `8` alcanza a todo vértice. -/
theorem cellGraph_reachable_from_center (a : Fin 9) : cellGraph.Reachable 8 a := by
  have h : a = 8 ∨ cellAdj 8 a := by
    fin_cases a <;> (first | exact Or.inl rfl | exact Or.inr (Or.inl (by decide)))
  rcases h with h | h
  · subst h; exact SimpleGraph.Reachable.refl 8
  · exact SimpleGraph.Adj.reachable h
/-- **Certificado (Grafo conexo)**: `cellGraph` es conexo. -/
theorem cellGraph_connected : cellGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · intro u v
    exact (cellGraph_reachable_center u).trans (cellGraph_reachable_from_center v)
  · exact ⟨0⟩
/-- Decidabilidad explícita de la adyacencia (para cómputos). -/
instance instDecidableCellAdj : DecidableRel cellAdj :=
  fun a b => inferInstanceAs (Decidable ((a, b) ∈ cellEdgeList ∨ (b, a) ∈ cellEdgeList))
/-- **Certificado (grado del centro)**: el centro `8` tiene grado `8`. -/
theorem cellGraph_deg_center :
    (Finset.univ.filter (fun b : Fin 9 => cellGraph.Adj 8 b)).card = 8 := by
  change (Finset.univ.filter (fun b : Fin 9 => cellAdj 8 b)).card = 8
  decide
/-- **Certificado (grado de esquina)**: cada esquina tiene grado `4` (3 del cubo + centro). -/
theorem cellGraph_deg_corner (a : Fin 8) :
    (Finset.univ.filter (fun b : Fin 9 => cellGraph.Adj a.castSucc b)).card = 4 := by
  change (Finset.univ.filter (fun b : Fin 9 => cellAdj a.castSucc b)).card = 4
  fin_cases a <;> decide
/-- **Certificado (unicidad del centro)**: el único vértice de grado `8` es el centro. -/
theorem cellGraph_deg8_unique (b : Fin 9) :
    (Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj b c)).card = 8 → b = 8 := by
  fin_cases b <;> decide
/-- **Certificado (clases por grado)**: hay exactamente `1` vértice de grado `8` (el centro). -/
theorem cellGraph_count_deg8 :
    (Finset.univ.filter
      (fun b : Fin 9 => (Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj b c)).card = 8)).card = 1 := by
  decide
/-- **Certificado (clases por grado)**: hay exactamente `8` vértices de grado `4` (las esquinas). -/
theorem cellGraph_count_deg4 :
    (Finset.univ.filter
      (fun b : Fin 9 => (Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj b c)).card = 4)).card = 8 := by
  decide
/-- **Certificado (el automorfismo fija el centro)**: todo isomorfismo `cellGraph ≃g cellGraph` fija el centro `8`
    (preserva adyacencia y el centro es el único de grado 8). -/
theorem cellGraph_iso_fixes_center (f : cellGraph ≃g cellGraph) : f 8 = 8 := by
  apply cellGraph_deg8_unique
  have h : (Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj (f 8) c)).card
      = (Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj 8 c)).card := by
    refine Finset.card_bij (fun c _ => f.symm c) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      show cellGraph.Adj 8 (f.symm a)
      rw [← SimpleGraph.Iso.map_adj_iff f]
      simpa using ha
    · intro a _ b _ hab
      exact f.symm.injective hab
    · intro b hb
      refine ⟨f b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        show cellGraph.Adj (f 8) (f b)
        rw [SimpleGraph.Iso.map_adj_iff f]
        exact hb
      · simp
  rw [h, cellGraph_deg_center]
/-- **Certificado (tipos de aristas)**: en la celda hay `12` aristas cubo–cubo (esquina–esquina)
    y `8` aristas centro–esquina. -/
theorem cellEdgeList_types :
    (cellEdgeList.filter (fun p : Fin 9 × Fin 9 => p.1.val < 8 ∧ p.2.val < 8)).length = 12 ∧
    (cellEdgeList.filter (fun p : Fin 9 × Fin 9 => p.1.val = 8 ∨ p.2.val = 8)).length = 8 := by
  constructor <;> decide
/-- **Certificado (vecinos de una esquina)**: cada esquina tiene 3 vecinas esquinas + el centro. -/
theorem cellGraph_corner_neighbors (a : Fin 8) :
    ((Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj a.castSucc c ∧ c.val < 8)).card = 3) ∧
    ((Finset.univ.filter (fun c : Fin 9 => cellGraph.Adj a.castSucc c ∧ c.val = 8)).card = 1) := by
  fin_cases a <;> decide
/-! ### Automorfismo explícito de la celda (intercambio y↔z) -/
/-- Permutación de la celda: intercambia los dos bits bajos de las esquinas (`y↔z`) y fija el centro. -/
def swapYZFun (n : Fin 9) : Fin 9 :=
  if h : n.val < 8 then ⟨4 * (n.val / 4) + 2 * (n.val % 2) + (n.val / 2) % 2, by omega⟩
  else 8
theorem swapYZFun_inj : Function.Injective swapYZFun := by decide
theorem swapYZFun_surj : Function.Surjective swapYZFun := by decide
/-- La permutación `y↔z` como equivalencia. -/
noncomputable def swapYZEquiv : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective swapYZFun ⟨swapYZFun_inj, swapYZFun_surj⟩
theorem swapYZEquiv_apply (u : Fin 9) : swapYZEquiv u = swapYZFun u := rfl
/-- La permutación `y↔z` preserva la adyacencia. -/
theorem swapYZEquiv_adj : ∀ u v : Fin 9, cellGraph.Adj (swapYZEquiv u) (swapYZEquiv v) ↔ cellGraph.Adj u v := by
  intro u v
  rw [swapYZEquiv_apply u, swapYZEquiv_apply v]
  fin_cases u <;> fin_cases v <;> decide
/-- **Certificado (automorfismo)**: el intercambio `y↔z` es un automorfismo del grafo de la celda. -/
noncomputable def swapYZIso : cellGraph ≃g cellGraph where
  toEquiv := swapYZEquiv
  map_rel_iff' := fun {a b} => swapYZEquiv_adj a b
/-! ### Volteos (traslaciones del cubo) y transitividad de esquinas -/
/-- Volteo de bits de las esquinas según `d` (el centro queda fijo). -/
def flipFun (d : Fin 8) (n : Fin 9) : Fin 9 :=
  if h : n.val < 8 then
    ⟨n.val ^^^ d.val, by
      have h1 : n.val < 2 ^ 3 := by omega
      have h2 : d.val < 2 ^ 3 := by omega
      have h3 : n.val ^^^ d.val < 2 ^ 3 := Nat.xor_lt_two_pow h1 h2
      omega⟩
  else 8
theorem flipFun_inj : ∀ d : Fin 8, Function.Injective (flipFun d) := by decide
theorem flipFun_surj : ∀ d : Fin 8, Function.Surjective (flipFun d) := by decide
theorem flipFun_adj :
    ∀ (d : Fin 8) (u v : Fin 9), cellGraph.Adj (flipFun d u) (flipFun d v) ↔ cellGraph.Adj u v := by
  decide
/-- **Certificado (automorfismo de volteo)**: cada volteo `d` es un automorfismo de la celda. -/
noncomputable def flipIso (d : Fin 8) : cellGraph ≃g cellGraph where
  toEquiv := Equiv.ofBijective (flipFun d) ⟨flipFun_inj d, flipFun_surj d⟩
  map_rel_iff' := fun {a b} => flipFun_adj d a b
theorem flipIso_apply (d : Fin 8) (n : Fin 9) : flipIso d n = flipFun d n := rfl
/-- **Certificado (transitividad de esquinas)**: para toda esquina `b` hay un automorfismo que lleva
    la esquina `0` a `b`. Con `cellGraph_iso_fixes_center`, las 8 esquinas forman UNA órbita. -/
theorem cellGraph_corner0_reaches (b : Fin 8) :
    ∃ f : cellGraph ≃g cellGraph, f (0 : Fin 8).castSucc = b.castSucc := by
  refine ⟨flipIso b, ?_⟩
  rw [flipIso_apply]
  fin_cases b <;> decide
/-- Aplicación del volteo (para esquinas): `(flipFun d n).val = n.val ^^^ d.val`. -/
theorem flipFun_apply_lt (d : Fin 8) (n : Fin 9) (h : n.val < 8) :
    (flipFun d n).val = n.val ^^^ d.val := by
  unfold flipFun
  rw [dif_pos h]
/-- **Certificado (vertex-transitividad completa de las esquinas)**: dadas dos esquinas cualesquiera
    `a`, `b`, existe un automorfismo que lleva `a` a `b` (el volteo por `a xor b`).
    Es decir: **las 8 esquinas forman una única órbita** (una sola "forma"). -/
theorem cellGraph_corners_transitive (a b : Fin 8) :
    ∃ f : cellGraph ≃g cellGraph, f a.castSucc = b.castSucc := by
  refine ⟨flipIso ⟨a.val ^^^ b.val, by
    have h1 : a.val < 2 ^ 3 := by omega
    have h2 : b.val < 2 ^ 3 := by omega
    have h3 : a.val ^^^ b.val < 2 ^ 3 := Nat.xor_lt_two_pow h1 h2
    omega⟩, ?_⟩
  rw [flipIso_apply]
  
  
  fin_cases a <;> fin_cases b <;> decide
/-! ### La "celda doble": 2 celdas compartiendo 1 esquina (estructura del par) -/
/-- Inclusión de la 1ª celda en el par (17 vértices): `0..7` y `8` se conservan. -/
def pairF1 (n : Fin 9) : Fin 17 := ⟨n.val, by omega⟩
/-- Inclusión de la 2ª celda: su esquina `0` ES la esquina `0` compartida; `1..7 → 9..15`; centro `→ 16`. -/
def pairF2 (n : Fin 9) : Fin 17 :=
  if n.val = 8 then 16 else if n.val = 0 then 0 else ⟨n.val + 8, by omega⟩
/-- **Aristas del par** (2 celdas compartiendo 1 esquina): 20 + 20 = 40. -/
def pairEdgeList : List (Fin 17 × Fin 17) :=
  cellEdgeList.map (fun p => (pairF1 p.1, pairF1 p.2)) ++
  cellEdgeList.map (fun p => (pairF2 p.1, pairF2 p.2))
/-- **Certificado**: el par tiene `40` aristas (dos celdas de 20). -/
theorem pair_edges : pairEdgeList.length = 40 := by
  simp [pairEdgeList, cellGraph_edges]
/-- **Certificado**: cada mitad aporta 20 aristas. -/
theorem pair_halves :
    (cellEdgeList.map (fun p => (pairF1 p.1, pairF1 p.2))).length = 20 ∧
    (cellEdgeList.map (fun p => (pairF2 p.1, pairF2 p.2))).length = 20 := by
  constructor <;> simp [cellGraph_edges]
/-- **Certificado (invariantes del par)**: `V=17`, `E=40`, `beta_1 = 40-17+1 = 24`
    — coincide con la Línea de trabajo 5 (estructura de esquina compartida). -/
theorem pair_invariants :
    (Fintype.card (Fin 17), pairEdgeList.length, pairEdgeList.length - Fintype.card (Fin 17) + 1)
      = (17, 40, 24) := by
  simp [pairEdgeList, cellGraph_edges]
/-! ### Celda doble con ARISTA compartida (V=16, E=39) -/
/-- Inclusión de la 1ª celda en el par-arista (`Fin 16`). -/
def pairEA1 (n : Fin 9) : Fin 16 := ⟨n.val, by omega⟩
/-- Inclusión de la 2ª celda compartiendo la ARISTA `0-1`; libres `2..7 → 9..14`; centro `→ 15`. -/
def pairEA2 (n : Fin 9) : Fin 16 :=
  if n.val = 8 then 15 else if n.val = 0 then 0 else if n.val = 1 then 1 else ⟨n.val + 7, by omega⟩
/-- **Aristas del par-arista** (con deduplicación: la arista compartida cuenta 1 vez). -/
def pairEAEdges : List (Fin 16 × Fin 16) :=
  cellEdgeList.map (fun p => (pairEA1 p.1, pairEA1 p.2)) ++
  cellEdgeList.map (fun p => (pairEA2 p.1, pairEA2 p.2))
/-- **Certificado (arista compartida)**: `V=16`, `E=39` (40 − 1 compartida), `beta_1 = 24`. -/
theorem pairEA_invariants :
    (Fintype.card (Fin 16), pairEAEdges.dedup.length, pairEAEdges.dedup.length - Fintype.card (Fin 16) + 1)
      = (16, 39, 24) := by
  decide
/-! ### Celda doble con CARA compartida (V=14, E=36) -/
/-- Inclusión de la 1ª celda en el par-cara (`Fin 14`). -/
def pairFA1 (n : Fin 9) : Fin 14 := ⟨n.val, by omega⟩
/-- Inclusión de la 2ª celda compartiendo la CARA `0-1-2-3`; libres `4..7 → 9..12`; centro `→ 13`. -/
def pairFA2 (n : Fin 9) : Fin 14 :=
  if n.val = 8 then 13 else if n.val < 4 then ⟨n.val, by omega⟩ else ⟨n.val + 5, by omega⟩
/-- **Aristas del par-cara** (deduplicación: las 4 aristas de la cara cuentan 1 vez). -/
def pairFAEdges : List (Fin 14 × Fin 14) :=
  cellEdgeList.map (fun p => (pairFA1 p.1, pairFA1 p.2)) ++
  cellEdgeList.map (fun p => (pairFA2 p.1, pairFA2 p.2))
/-- **Certificado (cara compartida)**: `V=14`, `E=36` (40 − 4 compartidas), `beta_1 = 23`. -/
theorem pairFA_invariants :
    (Fintype.card (Fin 14), pairFAEdges.dedup.length, pairFAEdges.dedup.length - Fintype.card (Fin 14) + 1)
      = (14, 36, 23) := by
  decide
/-! ### La estrella de 3 lazos (3 celdas compartiendo la esquina 0) -/
/-- Inclusión de la 1ª celda en la estrella (`Fin 25`). -/
def starF1 (n : Fin 9) : Fin 25 := ⟨n.val, by omega⟩
/-- 2ª celda de la estrella (comparte el nodo `0`). -/
def starF2 (n : Fin 9) : Fin 25 := if n.val = 8 then 16 else if n.val = 0 then 0 else ⟨n.val + 8, by omega⟩
/-- 3ª celda de la estrella (comparte el nodo `0`). -/
def starF3 (n : Fin 9) : Fin 25 := if n.val = 8 then 24 else if n.val = 0 then 0 else ⟨n.val + 16, by omega⟩
/-- **Aristas de la estrella** (3 celdas compartiendo la esquina `0`). -/
def starEdgeList : List (Fin 25 × Fin 25) :=
  cellEdgeList.map (fun p => (starF1 p.1, starF1 p.2)) ++
  cellEdgeList.map (fun p => (starF2 p.1, starF2 p.2)) ++
  cellEdgeList.map (fun p => (starF3 p.1, starF3 p.2))
/-- **Certificado (estrella de 3 lazos)**: `V=25`, `E=60`, `beta_1 = 36`. -/
theorem star_invariants :
    (Fintype.card (Fin 25), starEdgeList.dedup.length, starEdgeList.dedup.length - Fintype.card (Fin 25) + 1)
      = (25, 60, 36) := by
  decide
/-- **Certificado (aditividad estructural)**: los 3 anillos z de la estrella se intersecan
    SOLO en el nodo `0` — por eso las energías por lazo son aditivas (v1.4). -/
theorem star_rings_touch_only_at_0 :
    ({0, 1, 3, 2} : Finset (Fin 25)) ∩ {0, 9, 11, 10} = {0} ∧
    ({0, 1, 3, 2} : Finset (Fin 25)) ∩ {0, 17, 19, 18} = {0} ∧
    ({0, 9, 11, 10} : Finset (Fin 25)) ∩ {0, 17, 19, 18} = {0} := by
  decide
/-! ### El matiz O (24) vs Aut (48): automorfismos del cubo -/
/-- Aristas del cubo (solo esquinas): pares que difieren en un bit (`XOR ∈ {1,2,4}`). -/
def cubeEdge (a b : Fin 8) : Prop := a ≠ b ∧ (a.val ^^^ b.val) ∈ ({1, 2, 4} : Finset ℕ)
instance instDecidableCubeEdge : DecidableRel cubeEdge :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (a.val ^^^ b.val) ∈ ({1, 2, 4} : Finset ℕ)))
/-- **Certificado (`|Aut| = 48`)**: los automorfismos del cubo (esquinas) son **48**
    (24 rotaciones propias + 24 impropias/reflexiones). Con `|O| = 24` (rotaciones, `TMTConfig`),
    esto respalda el matiz de la Investigación Toroidal: el `(C,T) = (3,8)` del electrón usa
    **O (24)** — órbita 3 × estabilizador 8 — no el grupo completo (daría `(3,16)`). -/
theorem cube_aut_card :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 8) =>
      ∀ u v : Fin 8, cubeEdge u v ↔ cubeEdge (σ u) (σ v))).card = 48 := by
  native_decide
/-! ### La estructura de 11 nodos (candidato ρ/B: 2 celdas compartiendo 7 esquinas) -/
/-- Inclusión de la 1ª celda en la estructura de 11 (`Fin 11`). -/
def n11F1 (n : Fin 9) : Fin 11 := ⟨n.val, by omega⟩
/-- 2ª celda: comparte las esquinas `0..6`; su esquina `7 → 9`; su centro `→ 10`. -/
def n11F2 (n : Fin 9) : Fin 11 :=
  if n.val = 8 then 10 else if n.val = 7 then 9 else ⟨n.val, by omega⟩
/-- **Aristas**: 2 celdas compartiendo 7 esquinas. -/
def n11EdgeList : List (Fin 11 × Fin 11) :=
  cellEdgeList.map (fun p => (n11F1 p.1, n11F1 p.2)) ++
  cellEdgeList.map (fun p => (n11F2 p.1, n11F2 p.2))
/-- **Certificado (estructura de 11 nodos, candidato ρ/B)**: `V=11`, `E=31`, `beta_1 = 21`
    — coincide con la construcción de la Investigación Toroidal (doc 36/37: T=11 por la regla nº nodos). -/
theorem n11_invariants :
    (Fintype.card (Fin 11), n11EdgeList.dedup.length, n11EdgeList.dedup.length - Fintype.card (Fin 11) + 1)
      = (11, 31, 21) := by
  decide
end TIE.TMT
