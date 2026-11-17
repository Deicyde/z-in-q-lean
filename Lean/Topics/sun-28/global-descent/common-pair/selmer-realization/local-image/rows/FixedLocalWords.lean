import Mathlib.Tactic.IntervalCases

namespace Sun28.FixedLocalRows
set_option linter.unusedSimpArgs false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩

/-- The low ten bits encode a, the high ten b. In each block the generators
are -1, 2, 3, 11, 109, 439, 283, 1433, 4373 and 14557 in that order. -/
abbrev Word := BitVec 20

/-- The two unit characters for each of the seven primes dividing n, followed
by positivity of a, even valuation of b at 2, and b square over Q₃. -/
def localEquations (v : Word) : Prop :=
    (v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 8) = false ∧
    (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) = false ∧
    (v.getLsbD 1 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 8) = false ∧
    (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) = false ∧
    (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) = false ∧
    (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) = false ∧
    (v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 8 ^^ v.getLsbD 9 ^^ v.getLsbD 16) = false ∧
    (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) = false ∧
    (v.getLsbD 2 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 17) = false ∧
    (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) = false ∧
    (v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 9 ^^ v.getLsbD 18) = false ∧
    (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) = false ∧
    (v.getLsbD 1 ^^ v.getLsbD 6 ^^ v.getLsbD 8) = false ∧
    (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) = false ∧
    (v.getLsbD 0) = false ∧
    (v.getLsbD 11) = false ∧
    (v.getLsbD 12) = false ∧
    (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18) = false

private theorem same (a b : Bool) : ((a ^^ b) = false) ↔ a = b := by cases a <;> cases b <;> decide

/-- Rank seventeen, with three free coordinates. Each row of the reduced system is a specified XOR of the original equations. -/
theorem reduced (v : Word) (h : localEquations v) :
    v.getLsbD 0 = false ∧
    v.getLsbD 1 = false ∧
    v.getLsbD 4 = (v.getLsbD 3) ∧
    v.getLsbD 5 = (v.getLsbD 3) ∧
    v.getLsbD 7 = (v.getLsbD 6) ∧
    v.getLsbD 8 = (v.getLsbD 6) ∧
    v.getLsbD 9 = (v.getLsbD 6) ∧
    v.getLsbD 10 = (v.getLsbD 2) ∧
    v.getLsbD 11 = false ∧
    v.getLsbD 12 = false ∧
    v.getLsbD 13 = (v.getLsbD 2) ∧
    v.getLsbD 14 = (v.getLsbD 2) ∧
    v.getLsbD 15 = (v.getLsbD 2) ∧
    v.getLsbD 16 = (v.getLsbD 2) ∧
    v.getLsbD 17 = (v.getLsbD 2) ∧
    v.getLsbD 18 = (v.getLsbD 2) ∧
    v.getLsbD 19 = (v.getLsbD 2) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17⟩
  have r0 := h14
  have a0 : (v.getLsbD 0) = false := by
    calc
      _ = ((v.getLsbD 0)) := by ac_rfl
      _ = false := r0
  have e0 : v.getLsbD 0 = false := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false] using a0
  have r1 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h17)
  have a1 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 3 ^^ v.getLsbD 3) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 5 ^^ v.getLsbD 5) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 7 ^^ v.getLsbD 7) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ (v.getLsbD 9 ^^ v.getLsbD 9) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 1) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 1 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 8 ^^ v.getLsbD 9 ^^ v.getLsbD 16) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 2 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 17) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 9 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 1 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r1
  have e1 : v.getLsbD 1 = false := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false] using a1
  have r4 := (congrArg₂ Bool.xor h2 h12)
  have a4 : ((v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ v.getLsbD 4 ^^ v.getLsbD 3) = false := by
    calc
      _ = ((v.getLsbD 1 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 1 ^^ v.getLsbD 6 ^^ v.getLsbD 8)) := by ac_rfl
      _ = false := r4
  have e4 : v.getLsbD 4 = (v.getLsbD 3) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a4
  have r5 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor h0 h2) h14)
  have a5 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ v.getLsbD 5 ^^ v.getLsbD 3) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 1 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 0)) := by ac_rfl
      _ = false := r5
  have e5 : v.getLsbD 5 = (v.getLsbD 3) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a5
  have r7 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h1 h3) h4) h5) h7) h8) h9) h11) h14) h15) h17)
  have a7 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 7 ^^ v.getLsbD 6) = false := by
    calc
      _ = ((v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 2 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 17) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 0) ^^ (v.getLsbD 11) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r7
  have e7 : v.getLsbD 7 = (v.getLsbD 6) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a7
  have r8 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h13) h14) h17)
  have a8 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 3 ^^ v.getLsbD 3) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 5 ^^ v.getLsbD 5) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 7 ^^ v.getLsbD 7) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ (v.getLsbD 9 ^^ v.getLsbD 9) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 8 ^^ v.getLsbD 6) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 1 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 8 ^^ v.getLsbD 9 ^^ v.getLsbD 16) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 2 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 17) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 3 ^^ v.getLsbD 4 ^^ v.getLsbD 6 ^^ v.getLsbD 9 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r8
  have e8 : v.getLsbD 8 = (v.getLsbD 6) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a8
  have r9 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h0 h1) h3) h5) h6) h8) h9)
  have a9 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 1 ^^ v.getLsbD 1) ^^ (v.getLsbD 2 ^^ v.getLsbD 2) ^^ (v.getLsbD 4 ^^ v.getLsbD 4) ^^ (v.getLsbD 5 ^^ v.getLsbD 5) ^^ (v.getLsbD 6 ^^ v.getLsbD 6) ^^ (v.getLsbD 7 ^^ v.getLsbD 7) ^^ (v.getLsbD 8 ^^ v.getLsbD 8) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 9 ^^ v.getLsbD 6) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 8) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 0 ^^ v.getLsbD 1 ^^ v.getLsbD 2 ^^ v.getLsbD 4 ^^ v.getLsbD 5 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 8 ^^ v.getLsbD 9 ^^ v.getLsbD 16) ^^ (v.getLsbD 2 ^^ v.getLsbD 6 ^^ v.getLsbD 7 ^^ v.getLsbD 17) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17)) := by ac_rfl
      _ = false := r9
  have e9 : v.getLsbD 9 = (v.getLsbD 6) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a9
  have r10 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h1 h3) h4) h14)
  have a10 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 10 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 0)) := by ac_rfl
      _ = false := r10
  have e10 : v.getLsbD 10 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a10
  have r11 := h15
  have a11 : (v.getLsbD 11) = false := by
    calc
      _ = ((v.getLsbD 11)) := by ac_rfl
      _ = false := r11
  have e11 : v.getLsbD 11 = false := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false] using a11
  have r12 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor h1 h3) h5)
  have a12 : ((v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 12) = false := by
    calc
      _ = ((v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15)) := by ac_rfl
      _ = false := r12
  have e12 : v.getLsbD 12 = false := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false] using a12
  have r13 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h4 h5) h9) h13) h14) h17)
  have a13 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 13 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r13
  have e13 : v.getLsbD 13 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a13
  have r14 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h3 h4) h5) h9) h14) h17)
  have a14 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 14 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r14
  have e14 : v.getLsbD 14 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a14
  have r15 := (congrArg₂ Bool.xor h4 h14)
  have a15 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ v.getLsbD 15 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 0)) := by ac_rfl
      _ = false := r15
  have e15 : v.getLsbD 15 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a15
  have r16 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h4 h7) h11) h14) h15) h17)
  have a16 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 16 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 0) ^^ (v.getLsbD 11) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r16
  have e16 : v.getLsbD 16 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a16
  have r17 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h1 h3) h4) h5) h7) h9) h11) h14) h15) h17)
  have a17 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 17 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 12 ^^ v.getLsbD 16 ^^ v.getLsbD 17) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 0) ^^ (v.getLsbD 11) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r17
  have e17 : v.getLsbD 17 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a17
  have r18 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h4 h7) h11) h13) h14) h17)
  have a18 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 19 ^^ v.getLsbD 19) ^^ v.getLsbD 18 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 16 ^^ v.getLsbD 19) ^^ (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r18
  have e18 : v.getLsbD 18 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a18
  have r19 := (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor (congrArg₂ Bool.xor h1 h4) h5) h7) h13) h14) h17)
  have a19 : ((v.getLsbD 0 ^^ v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 10 ^^ v.getLsbD 10) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 11 ^^ v.getLsbD 11) ^^ (v.getLsbD 12 ^^ v.getLsbD 12) ^^ (v.getLsbD 13 ^^ v.getLsbD 13) ^^ (v.getLsbD 14 ^^ v.getLsbD 14) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 15 ^^ v.getLsbD 15) ^^ (v.getLsbD 16 ^^ v.getLsbD 16) ^^ (v.getLsbD 17 ^^ v.getLsbD 17) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ (v.getLsbD 18 ^^ v.getLsbD 18) ^^ v.getLsbD 19 ^^ v.getLsbD 2) = false := by
    calc
      _ = ((v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0 ^^ v.getLsbD 2 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 12 ^^ v.getLsbD 15) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 12 ^^ v.getLsbD 14 ^^ v.getLsbD 15 ^^ v.getLsbD 17 ^^ v.getLsbD 18 ^^ v.getLsbD 19) ^^ (v.getLsbD 11 ^^ v.getLsbD 16 ^^ v.getLsbD 18) ^^ (v.getLsbD 0) ^^ (v.getLsbD 10 ^^ v.getLsbD 11 ^^ v.getLsbD 13 ^^ v.getLsbD 17 ^^ v.getLsbD 18)) := by ac_rfl
      _ = false := r19
  have e19 : v.getLsbD 19 = (v.getLsbD 2) := by
    simpa only [Bool.xor_self, Bool.false_xor, Bool.xor_false, same] using a19
  exact ⟨e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19⟩

theorem eight_words (v : Word) : localEquations v ↔
    v = 0 ∨
    v = 56 ∨
    v = 960 ∨
    v = 1016 ∨
    v = 1041412 ∨
    v = 1041468 ∨
    v = 1042372 ∨
    v = 1042428 := by
  constructor
  · intro h
    obtain ⟨e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19⟩ := reduced v h
    cases f2 : v.getLsbD 2 <;> cases f3 : v.getLsbD 3 <;> cases f6 : v.getLsbD 6
    · have word : v = 0 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 960 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 56 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 1016 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 1041412 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 1042372 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 1041468 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
    · have word : v = 1042428 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        interval_cases i <;> simp only [e0,e1,e4,e5,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,f2,f3,f6,Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] <;> rfl
      simp [word]
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold localEquations <;> decide

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.reduced
#print axioms Sun28.FixedLocalRows.eight_words
