/-
B6 — SPARC: álgebra del puente implícito g_bar = g·μ(g/a) con μ(x)=x/√(1+x²).
Carpeta: tie-review/teoria-abierta/B6-SPARC-test/
Resultado: la ecuación implícita equivale a la cuadrática u² - g_bar²u - g_bar²a² = 0 (u = g²),
cuya raíz física es u = (g_bar² + g_bar√(g_bar²+4a²))/2.
-/
import Mathlib
namespace TIE.B6
/-- **B6 — puente implícito ⇒ cuadrática**: si `u = g²` satisface `u = g_bar·√(u+a²)`,
entonces `u² − g_bar²u − g_bar²a² = 0` (la ecuación que resuelve el ajuste SPARC). -/
theorem bridge_quadratic (gb u a : ℝ) (h0 : 0 ≤ u + a^2)
    (h : u = gb * Real.sqrt (u + a^2)) :
    u^2 - gb^2 * u - gb^2 * a^2 = 0 := by
  have h2 : u^2 = gb^2 * (u + a^2) := by
    nth_rewrite 1 [h]
    rw [mul_pow, Real.sq_sqrt h0]
  nlinarith [h2]
/-- **B6 — raíz física cerrada**: `u = (g_bar² + g_bar√(g_bar²+4a²))/2` resuelve la cuadrática
(es la rama positiva que usa el ajuste). -/
theorem bridge_solution (gb a : ℝ) (hgb : 0 ≤ gb) (ha : 0 ≤ a) :
    ((gb^2 + gb * Real.sqrt (gb^2 + 4*a^2)) / 2)^2
      - gb^2 * ((gb^2 + gb * Real.sqrt (gb^2 + 4*a^2)) / 2)
      - gb^2 * a^2 = 0 := by
  have hs : (Real.sqrt (gb^2 + 4*a^2))^2 = gb^2 + 4*a^2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [hs]
end TIE.B6
