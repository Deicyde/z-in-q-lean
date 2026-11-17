import FixedLocalWords
import Mathlib.Tactic.NormNum.LegendreSymbol
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Sun28.FixedLocalRows

/-- Signed integer pair represented by the two ten-bit blocks. -/
def generatorProduct : List ℤ → Nat → Word → ℤ
  | [], _, _ => 1
  | a :: s, i, v => (if v.getLsbD i then a else 1) * generatorProduct s (i+1) v

def labels (v : Word) : ℤ × ℤ :=
  (generatorProduct [-1,2,3,11,109,439,283,1433,4373,14557] 0 v, generatorProduct [-1,2,3,11,109,439,283,1433,4373,14557] 10 v)

/-- A bit is set exactly when its generator contributes a nontrivial quadratic
character of the p-adic unit part. The roots have order (x+3n,x-n). -/
def symbol (p : ℕ) (a : ℤ) : Bool := decide (jacobiSym a p = -1)
def unitFactor (p : ℕ) (a : ℤ) : ℤ := if (p:ℤ) ∣ a then a/p else a
def accumulate : List Bool → Nat → Word → Bool → Bool
  | [], _, _, sum => sum
  | c :: s, i, v, sum => accumulate s (i+1) v (sum ^^ (if c then v.getLsbD i else false))

def bitDot (bs : List Bool) (i : Nat) (v : Word) := accumulate bs i v false

def localRow (p : ℕ) (second : Bool) : List Bool :=
  let n : ℤ := 13588380161692636619
  let low := [-1,2,3,11,109,439,283,1433,4373,14557].map fun (a : ℤ) =>
    if second then false else
      symbol p (unitFactor p a) ^^ (decide (a=(p:ℤ)) && symbol p (n/p))
  let high := [-1,2,3,11,109,439,283,1433,4373,14557].map fun (b : ℤ) =>
    if second then symbol p (unitFactor p b) ^^ (decide (b=(p:ℤ)) && symbol p (-(n/p)))
    else (decide (b=(p:ℤ)) && symbol p 3)
  low ++ high

def threeUnits : List Bool :=
  List.replicate 10 false ++ [-1,2,3,11,109,439,283,1433,4373,14557].map fun (b : ℤ) => symbol 3 (unitFactor 3 b)

/-- Necessary conditions on the signed units of the two divisor products. -/
def arithmeticEquations (v : Word) : Prop :=
  (([11,109,439,283,1433,4373,14557] : List Nat).zipIdx).all (fun (pj : Nat × Nat) =>
    !bitDot (localRow pj.1 false) 0 v && !bitDot (localRow pj.1 true) 0 v) = true ∧
    v.getLsbD 0 = false ∧ v.getLsbD 11 = false ∧ v.getLsbD 12 = false ∧
    bitDot threeUnits 0 v = false

private theorem row_11_a : localRow 11 false = [true,true,false,false,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_11_b : localRow 11 true = [false,false,false,false,false,false,false,false,false,false,true,true,false,true,true,true,true,false,true,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_109_a : localRow 109 false = [false,true,false,true,true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_109_b : localRow 109 true = [false,false,false,false,false,false,false,false,false,false,false,true,false,true,true,false,true,false,true,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_439_a : localRow 439 false = [true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_439_b : localRow 439 true = [false,false,false,false,false,false,false,false,false,false,true,false,true,false,false,true,false,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_283_a : localRow 283 false = [true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,false,true,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_283_b : localRow 283 true = [false,false,false,false,false,false,false,false,false,false,true,true,true,false,true,true,false,true,true,true] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_1433_a : localRow 1433 false = [false,false,true,false,false,false,true,true,false,false,false,false,false,false,false,false,false,true,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_1433_b : localRow 1433 true = [false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,true,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_4373_a : localRow 4373 false = [false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,true,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_4373_b : localRow 4373 true = [false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,true,false,false,true] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_14557_a : localRow 14557 false = [false,true,false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem row_14557_b : localRow 14557 true = [false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true,false,true,false] := by
  norm_num [localRow, unitFactor, symbol, List.map]

private theorem three_row : threeUnits = [false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,true,false] := by
  norm_num [threeUnits, symbol, unitFactor, List.map]

private theorem negated (b : Bool) : (!b) = true ↔ b=false := by cases b <;> decide

theorem equation_translation (v : Word) : arithmeticEquations v ↔ localEquations v := by
  simp only [arithmeticEquations, List.zipIdx, List.all_cons, List.all_nil, Bool.and_eq_true, negated,and_assoc, Bool.true_and, Bool.and_true, three_row,row_11_a,row_11_b,row_109_a,row_109_b,row_439_a,row_439_b,row_283_a,row_283_b,row_1433_a,row_1433_b,row_4373_a,row_4373_b,row_14557_a,row_14557_b]
  simp only [localEquations,bitDot,accumulate, Bool.xor_false,Bool.false_xor,ite_true,ite_false,Bool.false_eq_true,and_assoc,Nat.reduceAdd, true_and, and_true]

theorem eight_labels {v : Word} (h : arithmeticEquations v) : labels v ∈ ([(1,1),(526361,1),(25815704738179,1),(13588380161692636619,1),(3,-13588380161692636619),(1579083,-13588380161692636619),(77447114214537,-13588380161692636619),(40765140485077909857,-13588380161692636619)] : List (ℤ × ℤ)) := by
  have w := (eight_words v).mp ((equation_translation v).mp h)
  rcases w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.equation_translation
#print axioms Sun28.FixedLocalRows.eight_labels
