import Mathlib
import TieFormal.TMTRonda2
namespace TIE.TMT

/-- Normaliza un par (arista no dirigida). -/
def nor (p : ℕ × ℕ) : ℕ × ℕ := if p.1 ≤ p.2 then p else (p.2, p.1)

/-! ### P5 — linea-esquinas. -/
def LSN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (1,3), (1,5), (2,3), (2,6), (3,7), (4,5), (4,6), (4,8), (5,7), (5,9), (6,7), (6,10), (7,11), (8,9), (8,10), (8,12), (9,11), (9,13), (10,11), (10,14), (11,15), (12,13), (12,14), (13,15), (14,15)]
def LSa0v : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def LSa1v : List ℕ := [0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15]
def LSa2v : List ℕ := [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
def LSa3v : List ℕ := [1, 3, 0, 2, 5, 7, 4, 6, 9, 11, 8, 10, 13, 15, 12, 14]
def LSa4v : List ℕ := [2, 0, 3, 1, 6, 4, 7, 5, 10, 8, 11, 9, 14, 12, 15, 13]
def LSa5v : List ℕ := [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13]
def LSa6v : List ℕ := [3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10, 8, 15, 13, 14, 12]
def LSa7v : List ℕ := [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12]
def LSa8v : List ℕ := [12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]
def LSa9v : List ℕ := [12, 14, 13, 15, 8, 10, 9, 11, 4, 6, 5, 7, 0, 2, 1, 3]
def LSa10v : List ℕ := [13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2]
def LSa11v : List ℕ := [13, 15, 12, 14, 9, 11, 8, 10, 5, 7, 4, 6, 1, 3, 0, 2]
def LSa12v : List ℕ := [14, 12, 15, 13, 10, 8, 11, 9, 6, 4, 7, 5, 2, 0, 3, 1]
def LSa13v : List ℕ := [14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1]
def LSa14v : List ℕ := [15, 13, 14, 12, 11, 9, 10, 8, 7, 5, 6, 4, 3, 1, 2, 0]
def LSa15v : List ℕ := [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def LSnrepv : List ℕ := [0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0]
def LSerepN : List (ℕ × ℕ) := [(0,1), (0,1), (0,4), (0,1), (0,4), (0,1), (0,4), (0,4), (4,5), (4,5), (4,8), (4,5), (4,8), (4,5), (4,8), (4,8), (4,5), (4,5), (0,4), (4,5), (0,4), (4,5), (0,4), (0,4), (0,1), (0,1), (0,1), (0,1)]
def LSerepOf (p : ℕ × ℕ) : ℕ :=
  ((LSN.zip LSerepN).find? (fun q => q.1 = p)).map (fun q => q.2.1 * 100 + q.2.2) |>.getD 0
theorem p5_LS_a0 :
    (∀ e ∈ LSN, nor (LSa0v.getD e.1 0, LSa0v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa0v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa0v.getD e.1 0, LSa0v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a1 :
    (∀ e ∈ LSN, nor (LSa1v.getD e.1 0, LSa1v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa1v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa1v.getD e.1 0, LSa1v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a2 :
    (∀ e ∈ LSN, nor (LSa2v.getD e.1 0, LSa2v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa2v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa2v.getD e.1 0, LSa2v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a3 :
    (∀ e ∈ LSN, nor (LSa3v.getD e.1 0, LSa3v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa3v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa3v.getD e.1 0, LSa3v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a4 :
    (∀ e ∈ LSN, nor (LSa4v.getD e.1 0, LSa4v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa4v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa4v.getD e.1 0, LSa4v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a5 :
    (∀ e ∈ LSN, nor (LSa5v.getD e.1 0, LSa5v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa5v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa5v.getD e.1 0, LSa5v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a6 :
    (∀ e ∈ LSN, nor (LSa6v.getD e.1 0, LSa6v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa6v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa6v.getD e.1 0, LSa6v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a7 :
    (∀ e ∈ LSN, nor (LSa7v.getD e.1 0, LSa7v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa7v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa7v.getD e.1 0, LSa7v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a8 :
    (∀ e ∈ LSN, nor (LSa8v.getD e.1 0, LSa8v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa8v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa8v.getD e.1 0, LSa8v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a9 :
    (∀ e ∈ LSN, nor (LSa9v.getD e.1 0, LSa9v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa9v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa9v.getD e.1 0, LSa9v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a10 :
    (∀ e ∈ LSN, nor (LSa10v.getD e.1 0, LSa10v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa10v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa10v.getD e.1 0, LSa10v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a11 :
    (∀ e ∈ LSN, nor (LSa11v.getD e.1 0, LSa11v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa11v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa11v.getD e.1 0, LSa11v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a12 :
    (∀ e ∈ LSN, nor (LSa12v.getD e.1 0, LSa12v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa12v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa12v.getD e.1 0, LSa12v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a13 :
    (∀ e ∈ LSN, nor (LSa13v.getD e.1 0, LSa13v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa13v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa13v.getD e.1 0, LSa13v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a14 :
    (∀ e ∈ LSN, nor (LSa14v.getD e.1 0, LSa14v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa14v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa14v.getD e.1 0, LSa14v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_a15 :
    (∀ e ∈ LSN, nor (LSa15v.getD e.1 0, LSa15v.getD e.2 0) ∈ LSN) ∧
    (∀ v : Fin 16, LSnrepv.getD (LSa15v.getD v.val 0) 0 = LSnrepv.getD v.val 0) ∧
    (∀ e ∈ LSN, LSerepOf (nor (LSa15v.getD e.1 0, LSa15v.getD e.2 0)) = LSerepOf e) := by
  decide
theorem p5_LS_norb : (((List.range 16).filter (fun i => LSnrepv.getD i 0 = 0)).length = 8 ∧ ((List.range 16).filter (fun i => LSnrepv.getD i 0 = 4)).length = 8) := by decide
theorem p5_LS_eorb : ((LSN.filter (fun e => LSerepOf e = 1)).length = 8 ∧ (LSN.filter (fun e => LSerepOf e = 4)).length = 8 ∧ (LSN.filter (fun e => LSerepOf e = 405)).length = 8 ∧ (LSN.filter (fun e => LSerepOf e = 408)).length = 4) := by decide

/-! ### P5 — L-esquinas. -/
def LEN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (1,3), (1,5), (2,3), (2,6), (3,7), (4,5), (4,6), (4,8), (5,7), (5,9), (6,7), (6,10), (6,12), (7,11), (7,13), (8,9), (8,10), (9,11), (10,11), (10,14), (11,15), (12,13), (12,14), (13,15), (14,15)]
def LEa0v : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def LEa1v : List ℕ := [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
def LEa2v : List ℕ := [14, 15, 12, 13, 10, 11, 6, 7, 8, 9, 4, 5, 2, 3, 0, 1]
def LEa3v : List ℕ := [15, 14, 13, 12, 11, 10, 7, 6, 9, 8, 5, 4, 3, 2, 1, 0]
def LEnrepv : List ℕ := [0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 4, 4, 2, 2, 0, 0]
def LEerepN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (0,2), (0,4), (2,3), (2,6), (2,6), (4,5), (4,6), (4,8), (4,6), (4,8), (6,7), (4,6), (2,6), (4,6), (2,6), (8,9), (4,8), (4,8), (4,5), (0,4), (0,4), (2,3), (0,2), (0,2), (0,1)]
def LEerepOf (p : ℕ × ℕ) : ℕ :=
  ((LEN.zip LEerepN).find? (fun q => q.1 = p)).map (fun q => q.2.1 * 100 + q.2.2) |>.getD 0
theorem p5_LE_a0 :
    (∀ e ∈ LEN, nor (LEa0v.getD e.1 0, LEa0v.getD e.2 0) ∈ LEN) ∧
    (∀ v : Fin 16, LEnrepv.getD (LEa0v.getD v.val 0) 0 = LEnrepv.getD v.val 0) ∧
    (∀ e ∈ LEN, LEerepOf (nor (LEa0v.getD e.1 0, LEa0v.getD e.2 0)) = LEerepOf e) := by
  decide
theorem p5_LE_a1 :
    (∀ e ∈ LEN, nor (LEa1v.getD e.1 0, LEa1v.getD e.2 0) ∈ LEN) ∧
    (∀ v : Fin 16, LEnrepv.getD (LEa1v.getD v.val 0) 0 = LEnrepv.getD v.val 0) ∧
    (∀ e ∈ LEN, LEerepOf (nor (LEa1v.getD e.1 0, LEa1v.getD e.2 0)) = LEerepOf e) := by
  decide
theorem p5_LE_a2 :
    (∀ e ∈ LEN, nor (LEa2v.getD e.1 0, LEa2v.getD e.2 0) ∈ LEN) ∧
    (∀ v : Fin 16, LEnrepv.getD (LEa2v.getD v.val 0) 0 = LEnrepv.getD v.val 0) ∧
    (∀ e ∈ LEN, LEerepOf (nor (LEa2v.getD e.1 0, LEa2v.getD e.2 0)) = LEerepOf e) := by
  decide
theorem p5_LE_a3 :
    (∀ e ∈ LEN, nor (LEa3v.getD e.1 0, LEa3v.getD e.2 0) ∈ LEN) ∧
    (∀ v : Fin 16, LEnrepv.getD (LEa3v.getD v.val 0) 0 = LEnrepv.getD v.val 0) ∧
    (∀ e ∈ LEN, LEerepOf (nor (LEa3v.getD e.1 0, LEa3v.getD e.2 0)) = LEerepOf e) := by
  decide
theorem p5_LE_norb : (((List.range 16).filter (fun i => LEnrepv.getD i 0 = 0)).length = 4 ∧ ((List.range 16).filter (fun i => LEnrepv.getD i 0 = 2)).length = 4 ∧ ((List.range 16).filter (fun i => LEnrepv.getD i 0 = 4)).length = 4 ∧ ((List.range 16).filter (fun i => LEnrepv.getD i 0 = 6)).length = 2 ∧ ((List.range 16).filter (fun i => LEnrepv.getD i 0 = 8)).length = 2) := by decide
theorem p5_LE_eorb : ((LEN.filter (fun e => LEerepOf e = 1)).length = 2 ∧ (LEN.filter (fun e => LEerepOf e = 2)).length = 4 ∧ (LEN.filter (fun e => LEerepOf e = 4)).length = 4 ∧ (LEN.filter (fun e => LEerepOf e = 203)).length = 2 ∧ (LEN.filter (fun e => LEerepOf e = 206)).length = 4 ∧ (LEN.filter (fun e => LEerepOf e = 405)).length = 2 ∧ (LEN.filter (fun e => LEerepOf e = 406)).length = 4 ∧ (LEN.filter (fun e => LEerepOf e = 408)).length = 4 ∧ (LEN.filter (fun e => LEerepOf e = 607)).length = 1 ∧ (LEN.filter (fun e => LEerepOf e = 809)).length = 1) := by decide

/-! ### P5 — linea-poleas. -/
def PSN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (0,16), (1,3), (1,5), (1,16), (2,3), (2,6), (2,16), (3,7), (3,16), (4,5), (4,6), (4,8), (4,16), (4,17), (5,7), (5,9), (5,16), (5,17), (6,7), (6,10), (6,16), (6,17), (7,11), (7,16), (7,17), (8,9), (8,10), (8,12), (8,17), (8,18), (9,11), (9,13), (9,17), (9,18), (10,11), (10,14), (10,17), (10,18), (11,15), (11,17), (11,18), (12,13), (12,14), (12,18), (13,15), (13,18), (14,15), (14,18), (15,18)]
def PSa0v : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
def PSa1v : List ℕ := [0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15, 16, 17, 18]
def PSa2v : List ℕ := [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18]
def PSa3v : List ℕ := [1, 3, 0, 2, 5, 7, 4, 6, 9, 11, 8, 10, 13, 15, 12, 14, 16, 17, 18]
def PSa4v : List ℕ := [2, 0, 3, 1, 6, 4, 7, 5, 10, 8, 11, 9, 14, 12, 15, 13, 16, 17, 18]
def PSa5v : List ℕ := [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 16, 17, 18]
def PSa6v : List ℕ := [3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10, 8, 15, 13, 14, 12, 16, 17, 18]
def PSa7v : List ℕ := [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 16, 17, 18]
def PSa8v : List ℕ := [12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 18, 17, 16]
def PSa9v : List ℕ := [12, 14, 13, 15, 8, 10, 9, 11, 4, 6, 5, 7, 0, 2, 1, 3, 18, 17, 16]
def PSa10v : List ℕ := [13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 18, 17, 16]
def PSa11v : List ℕ := [13, 15, 12, 14, 9, 11, 8, 10, 5, 7, 4, 6, 1, 3, 0, 2, 18, 17, 16]
def PSa12v : List ℕ := [14, 12, 15, 13, 10, 8, 11, 9, 6, 4, 7, 5, 2, 0, 3, 1, 18, 17, 16]
def PSa13v : List ℕ := [14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 2, 3, 0, 1, 18, 17, 16]
def PSa14v : List ℕ := [15, 13, 14, 12, 11, 9, 10, 8, 7, 5, 6, 4, 3, 1, 2, 0, 18, 17, 16]
def PSa15v : List ℕ := [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 18, 17, 16]
def PSnrepv : List ℕ := [0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 16, 17, 16]
def PSerepN : List (ℕ × ℕ) := [(0,1), (0,1), (0,4), (0,16), (0,1), (0,4), (0,16), (0,1), (0,4), (0,16), (0,4), (0,16), (4,5), (4,5), (4,8), (4,16), (4,17), (4,5), (4,8), (4,16), (4,17), (4,5), (4,8), (4,16), (4,17), (4,8), (4,16), (4,17), (4,5), (4,5), (0,4), (4,17), (4,16), (4,5), (0,4), (4,17), (4,16), (4,5), (0,4), (4,17), (4,16), (0,4), (4,17), (4,16), (0,1), (0,1), (0,16), (0,1), (0,16), (0,1), (0,16), (0,16)]
def PSerepOf (p : ℕ × ℕ) : ℕ :=
  ((PSN.zip PSerepN).find? (fun q => q.1 = p)).map (fun q => q.2.1 * 100 + q.2.2) |>.getD 0
theorem p5_PS_a0 :
    (∀ e ∈ PSN, nor (PSa0v.getD e.1 0, PSa0v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa0v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa0v.getD e.1 0, PSa0v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a1 :
    (∀ e ∈ PSN, nor (PSa1v.getD e.1 0, PSa1v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa1v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa1v.getD e.1 0, PSa1v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a2 :
    (∀ e ∈ PSN, nor (PSa2v.getD e.1 0, PSa2v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa2v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa2v.getD e.1 0, PSa2v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a3 :
    (∀ e ∈ PSN, nor (PSa3v.getD e.1 0, PSa3v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa3v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa3v.getD e.1 0, PSa3v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a4 :
    (∀ e ∈ PSN, nor (PSa4v.getD e.1 0, PSa4v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa4v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa4v.getD e.1 0, PSa4v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a5 :
    (∀ e ∈ PSN, nor (PSa5v.getD e.1 0, PSa5v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa5v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa5v.getD e.1 0, PSa5v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a6 :
    (∀ e ∈ PSN, nor (PSa6v.getD e.1 0, PSa6v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa6v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa6v.getD e.1 0, PSa6v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a7 :
    (∀ e ∈ PSN, nor (PSa7v.getD e.1 0, PSa7v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa7v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa7v.getD e.1 0, PSa7v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a8 :
    (∀ e ∈ PSN, nor (PSa8v.getD e.1 0, PSa8v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa8v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa8v.getD e.1 0, PSa8v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a9 :
    (∀ e ∈ PSN, nor (PSa9v.getD e.1 0, PSa9v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa9v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa9v.getD e.1 0, PSa9v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a10 :
    (∀ e ∈ PSN, nor (PSa10v.getD e.1 0, PSa10v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa10v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa10v.getD e.1 0, PSa10v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a11 :
    (∀ e ∈ PSN, nor (PSa11v.getD e.1 0, PSa11v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa11v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa11v.getD e.1 0, PSa11v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a12 :
    (∀ e ∈ PSN, nor (PSa12v.getD e.1 0, PSa12v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa12v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa12v.getD e.1 0, PSa12v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a13 :
    (∀ e ∈ PSN, nor (PSa13v.getD e.1 0, PSa13v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa13v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa13v.getD e.1 0, PSa13v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a14 :
    (∀ e ∈ PSN, nor (PSa14v.getD e.1 0, PSa14v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa14v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa14v.getD e.1 0, PSa14v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_a15 :
    (∀ e ∈ PSN, nor (PSa15v.getD e.1 0, PSa15v.getD e.2 0) ∈ PSN) ∧
    (∀ v : Fin 19, PSnrepv.getD (PSa15v.getD v.val 0) 0 = PSnrepv.getD v.val 0) ∧
    (∀ e ∈ PSN, PSerepOf (nor (PSa15v.getD e.1 0, PSa15v.getD e.2 0)) = PSerepOf e) := by
  decide
theorem p5_PS_norb : (((List.range 19).filter (fun i => PSnrepv.getD i 0 = 0)).length = 8 ∧ ((List.range 19).filter (fun i => PSnrepv.getD i 0 = 4)).length = 8 ∧ ((List.range 19).filter (fun i => PSnrepv.getD i 0 = 16)).length = 2 ∧ ((List.range 19).filter (fun i => PSnrepv.getD i 0 = 17)).length = 1) := by decide
theorem p5_PS_eorb : ((PSN.filter (fun e => PSerepOf e = 1)).length = 8 ∧ (PSN.filter (fun e => PSerepOf e = 4)).length = 8 ∧ (PSN.filter (fun e => PSerepOf e = 16)).length = 8 ∧ (PSN.filter (fun e => PSerepOf e = 405)).length = 8 ∧ (PSN.filter (fun e => PSerepOf e = 408)).length = 4 ∧ (PSN.filter (fun e => PSerepOf e = 416)).length = 8 ∧ (PSN.filter (fun e => PSerepOf e = 417)).length = 8) := by decide

/-! ### P5 — L-poleas. -/
def PEN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (0,16), (1,3), (1,5), (1,16), (2,3), (2,6), (2,16), (3,7), (3,16), (4,5), (4,6), (4,8), (4,16), (4,17), (5,7), (5,9), (5,16), (5,17), (6,7), (6,10), (6,12), (6,16), (6,17), (6,18), (7,11), (7,13), (7,16), (7,17), (7,18), (8,9), (8,10), (8,17), (9,11), (9,17), (10,11), (10,14), (10,17), (10,18), (11,15), (11,17), (11,18), (12,13), (12,14), (12,18), (13,15), (13,18), (14,15), (14,18), (15,18)]
def PEa0v : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
def PEa1v : List ℕ := [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18]
def PEa2v : List ℕ := [14, 15, 12, 13, 10, 11, 6, 7, 8, 9, 4, 5, 2, 3, 0, 1, 18, 17, 16]
def PEa3v : List ℕ := [15, 14, 13, 12, 11, 10, 7, 6, 9, 8, 5, 4, 3, 2, 1, 0, 18, 17, 16]
def PEnrepv : List ℕ := [0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 4, 4, 2, 2, 0, 0, 16, 17, 16]
def PEerepN : List (ℕ × ℕ) := [(0,1), (0,2), (0,4), (0,16), (0,2), (0,4), (0,16), (2,3), (2,6), (2,16), (2,6), (2,16), (4,5), (4,6), (4,8), (4,16), (4,17), (4,6), (4,8), (4,16), (4,17), (6,7), (4,6), (2,6), (6,16), (6,17), (6,16), (4,6), (2,6), (6,16), (6,17), (6,16), (8,9), (4,8), (8,17), (4,8), (8,17), (4,5), (0,4), (4,17), (4,16), (0,4), (4,17), (4,16), (2,3), (0,2), (2,16), (0,2), (2,16), (0,1), (0,16), (0,16)]
def PEerepOf (p : ℕ × ℕ) : ℕ :=
  ((PEN.zip PEerepN).find? (fun q => q.1 = p)).map (fun q => q.2.1 * 100 + q.2.2) |>.getD 0
theorem p5_PE_a0 :
    (∀ e ∈ PEN, nor (PEa0v.getD e.1 0, PEa0v.getD e.2 0) ∈ PEN) ∧
    (∀ v : Fin 19, PEnrepv.getD (PEa0v.getD v.val 0) 0 = PEnrepv.getD v.val 0) ∧
    (∀ e ∈ PEN, PEerepOf (nor (PEa0v.getD e.1 0, PEa0v.getD e.2 0)) = PEerepOf e) := by
  decide
theorem p5_PE_a1 :
    (∀ e ∈ PEN, nor (PEa1v.getD e.1 0, PEa1v.getD e.2 0) ∈ PEN) ∧
    (∀ v : Fin 19, PEnrepv.getD (PEa1v.getD v.val 0) 0 = PEnrepv.getD v.val 0) ∧
    (∀ e ∈ PEN, PEerepOf (nor (PEa1v.getD e.1 0, PEa1v.getD e.2 0)) = PEerepOf e) := by
  decide
theorem p5_PE_a2 :
    (∀ e ∈ PEN, nor (PEa2v.getD e.1 0, PEa2v.getD e.2 0) ∈ PEN) ∧
    (∀ v : Fin 19, PEnrepv.getD (PEa2v.getD v.val 0) 0 = PEnrepv.getD v.val 0) ∧
    (∀ e ∈ PEN, PEerepOf (nor (PEa2v.getD e.1 0, PEa2v.getD e.2 0)) = PEerepOf e) := by
  decide
theorem p5_PE_a3 :
    (∀ e ∈ PEN, nor (PEa3v.getD e.1 0, PEa3v.getD e.2 0) ∈ PEN) ∧
    (∀ v : Fin 19, PEnrepv.getD (PEa3v.getD v.val 0) 0 = PEnrepv.getD v.val 0) ∧
    (∀ e ∈ PEN, PEerepOf (nor (PEa3v.getD e.1 0, PEa3v.getD e.2 0)) = PEerepOf e) := by
  decide
theorem p5_PE_norb : (((List.range 19).filter (fun i => PEnrepv.getD i 0 = 0)).length = 4 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 2)).length = 4 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 4)).length = 4 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 6)).length = 2 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 8)).length = 2 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 16)).length = 2 ∧ ((List.range 19).filter (fun i => PEnrepv.getD i 0 = 17)).length = 1) := by decide
theorem p5_PE_eorb : ((PEN.filter (fun e => PEerepOf e = 1)).length = 2 ∧ (PEN.filter (fun e => PEerepOf e = 2)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 4)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 16)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 203)).length = 2 ∧ (PEN.filter (fun e => PEerepOf e = 206)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 216)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 405)).length = 2 ∧ (PEN.filter (fun e => PEerepOf e = 406)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 408)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 416)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 417)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 607)).length = 1 ∧ (PEN.filter (fun e => PEerepOf e = 616)).length = 4 ∧ (PEN.filter (fun e => PEerepOf e = 617)).length = 2 ∧ (PEN.filter (fun e => PEerepOf e = 809)).length = 1 ∧ (PEN.filter (fun e => PEerepOf e = 817)).length = 2) := by decide

end TIE.TMT