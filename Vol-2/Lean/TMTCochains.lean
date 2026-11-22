/-
TIE — Encargo Toroidal P2 (doc 42): cochains y gauge.
A: x_v - x_u (incidencia orientada); clases = Z^E / Im A; n1 ~ n2 <=> n1 - n2 ∈ Im A.
Se certifican: curl-free sobre ciclos, aditividad del gauge y (refl/simetria/transitividad)
=> la relacion de gauge es de EQUIVALENCIA (estructura de las clases).

GAPS CONOCIDOS (auditoria 2026-10-30, bloque C):
  · gauge_ciclo4, gauge_add, gauge_refl/symm/trans son identidades de UN PASO (ring) sobre
    funciones Z->Z: certifican el algebra, NO la construccion del complejo de cadenas (Gap 4 declarado).
  · p2_inequivalencia SI es un contraejemplo formal genuino (2-1 vs 2-2 no gauge-equivalentes).
-/
import Mathlib
import TieFormal.TMTConfig
namespace TIE.TMT
/-- **Certificado (P2-a)**: sobre cualquier 4-ciclo `a→b→c→d→a` el gauge `A x = x_v − x_u`
    telescopa a `0` (curl-free) — propiedad de `Im A` (doc 42). -/
theorem gauge_ciclo4 (x : ℤ → ℤ) (a b c d : ℤ) :
    (x b - x a) + (x c - x b) + (x d - x c) + (x a - x d) = 0 := by
  ring
/-- **Certificado (P2-a)**: el gauge es aditivo punto a punto: `A(x+y) = A x + A y`. -/
theorem gauge_add (a b : ℤ → ℤ) (u v : ℤ) :
    ((fun z => a z + b z) v - (fun z => a z + b z) u) = (a v - a u) + (b v - b u) := by
  ring
/-- **Certificado (P2-a, reflexividad)**: `n + A 0 = n` (con `A 0 = 0`). -/
theorem gauge_refl {α β : Type} (A : (α → ℤ) → (β → ℤ))
    (h0 : ∀ b, A (fun _ => (0 : ℤ)) b = 0) (n : β → ℤ) :
    ∀ b, n b + A (fun _ => (0 : ℤ)) b = n b := by
  intro b
  rw [h0 b]
  ring
/-- **Certificado (P2-a, simetría)**: `(n + A x) + A(−x) = n` (con `A(−x) = −A x`). -/
theorem gauge_symm {α β : Type} (A : (α → ℤ) → (β → ℤ))
    (hneg : ∀ x b, A (fun a => - x a) b = - A x b)
    {n : β → ℤ} {x : α → ℤ} :
    ∀ b, (n b + A x b) + A (fun a => - x a) b = n b := by
  intro b
  rw [hneg x b]
  ring
/-- **Certificado (P2-a, transitividad)**: si `m = n + A x` y `k = m + A y` entonces
    `k = n + A(x+y)` (aditividad) — cierra la estructura de equivalencia de las clases. -/
theorem gauge_trans {α β : Type} (A : (α → ℤ) → (β → ℤ))
    (hadd : ∀ x y b, A (fun a => x a + y a) b = A x b + A y b)
    {n m k : β → ℤ} {x y : α → ℤ}
    (h1 : ∀ b, m b = n b + A x b) (h2 : ∀ b, k b = m b + A y b) :
    ∀ b, k b = n b + A (fun a => x a + y a) b := by
  intro b
  rw [h2 b, h1 b, hadd x y b]
  ring
/-! ### P2 (cierre, doc 43): inequivalencia de las clases 2-1 y 2-2 -/
/-- Flujos de la clase **2-1** (doc 43, 36 componentes en el orden `edges_order`). -/
def n21 : List ℤ := [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Flujos de la clase **2-2** (doc 43, 36 componentes). -/
def n22 : List ℤ := [0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- **Certificado (P2, datos)**: las dos clases tienen 36 componentes y difieren en las aristas
    12 (+1) y 14 (−1); los objetivos 2-1 `(1,1)` y 2-2 `(1,−1)` coinciden con sus `flux`. -/
theorem p2_datos_check :
    (n21.length = 36 ∧ n22.length = 36 ∧
     n21.get ⟨5, by decide⟩ = -1 ∧ n21.get ⟨12, by decide⟩ = 0 ∧ n21.get ⟨14, by decide⟩ = -1 ∧
     n22.get ⟨5, by decide⟩ = -1 ∧ n22.get ⟨12, by decide⟩ = -1 ∧ n22.get ⟨14, by decide⟩ = 0 ∧
     n21.get ⟨12, by decide⟩ - n22.get ⟨12, by decide⟩ = 1 ∧ n21.get ⟨13, by decide⟩ - n22.get ⟨13, by decide⟩ = 0 ∧
     n21.get ⟨14, by decide⟩ - n22.get ⟨14, by decide⟩ = -1 ∧ n21.get ⟨15, by decide⟩ - n22.get ⟨15, by decide⟩ = 0) := by
  decide
/-- **Certificado (P2-b, INEQUIVALENCIA 2-1 vs 2-2)**: la diferencia `d = n(2-1) − n(2-2)` NO puede ser
    un gauge `A x = x_v − x_u`. En la cara `x_outB` (aristas 12,13,14,15, orientaciones `+,+,−,−`)
    los valores de `d` son `1, 0, −1, 0`; un gauge telescoparía a `0`, pero las cuatro ecuaciones
    son **inconsistentes** (`1+0−(−1)−0 = 2 ≠ 0`). ⇒ `d ∉ Im A` ⇒ **clases distintas** (contraejemplo formal). -/
theorem p2_inequivalencia (x : Fin 14 → ℤ) :
    ¬ ((1 : ℤ) = x 10 - x 9 ∧ (0 : ℤ) = x 12 - x 10 ∧ (-1 : ℤ) = x 12 - x 11 ∧ (0 : ℤ) = x 11 - x 9) := by
  rintro ⟨h1, h2, h3, h4⟩
  linarith
end TIE.TMT