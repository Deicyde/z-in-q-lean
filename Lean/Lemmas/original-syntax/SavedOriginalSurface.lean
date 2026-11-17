import Mathlib.Tactic

/-! The small outer expressions of the saved V15 specification, decoded from its
pinned bytes. Call nodes remain distinct formal symbols with recorded source
rows, input-register numbers and private witness ranges. This file proves a
polynomial identity at this boundary and checks the five composition records. -/
namespace ManuscriptV15.Saved

inductive Gate
  | var (index : ℕ)
  | int (value : ℤ)
  | add (left right : ℕ)
  | mul (left right : ℕ)
  | ell
  | call (callee first : ℕ) (inputs : List ℕ)
  deriving Inhabited, DecidableEq

inductive Callee
  | library (n : ℕ)
  | recipe (name : String)
  deriving Inhabited, DecidableEq

structure Call where
  callee : Callee
  inputs : List ℕ
  first : ℕ
  witnesses : ℕ
  deriving Inhabited, DecidableEq

structure Recipe where
  name : String
  product : Bool
  parameters : ℕ
  witnesses : ℕ
  explicitRanges : List (ℕ × ℕ)
  calls : List Call
  deriving Inhabited, DecidableEq

-- BEGIN DECODED RECORDS
def multiplyNodes : Array Gate := #[
  .var 0,
  .var 1,
  .var 2,
  .var 3,
  .var 4,
  .var 5,
  .var 6,
  .var 7,
  .var 8,
  .var 9,
  .var 10,
  .var 11,
  .var 12,
  .var 13,
  .var 14,
  .int (0),
  .int (1),
  .int (-11243),
  .int (7950),
  .var 15,
  .int (8),
  .mul 20 19,
  .int (1641),
  .int (-145),
  .var 16,
  .int (4),
  .mul 25 24,
  .int (-15465),
  .var 17,
  .int (32),
  .mul 29 28,
  .int (87483),
  .var 18,
  .var 19,
  .var 20,
  .var 21,
  .var 22,
  .call 9 23 [15,19,23,24,28,32,33,34,35,36],
  .var 24,
  .var 25,
  .var 26,
  .var 27,
  .var 28,
  .call 9 29 [0,1,2,3,4,38,39,40,41,42],
  .var 30,
  .var 31,
  .var 32,
  .var 33,
  .var 34,
  .call 9 35 [5,6,7,8,9,44,45,46,47,48],
  .var 36,
  .var 37,
  .var 38,
  .var 39,
  .var 40,
  .call 9 41 [10,11,12,13,14,50,51,52,53,54],
  .ell,
  .call 8 42 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,56,32,33,34,35,36,38,39,40,41,42,44,45,46,47,48,50,51,52,53,54],
  .call 10 35148 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],
  .int (-1),
  .mul 59 22,
  .add 21 60,
  .mul 59 27,
  .add 26 62,
  .mul 59 31,
  .add 30 64,
  .mul 37 37,
  .mul 43 43,
  .mul 49 49,
  .mul 55 55,
  .mul 57 57,
  .mul 58 58,
  .add 66 67,
  .add 72 68,
  .add 73 69,
  .add 74 70,
  .add 75 71,
  .mul 61 61,
  .mul 63 63,
  .mul 65 65,
  .mul 76 76,
  .add 77 78,
  .add 81 79,
  .add 82 80]

def explicitMultiplyIndices : List ℕ := [15,16,17,18,19,20,21,22,24,25,26,27,28,30,31,32,33,34,36,37,38,39,40]
def recordedMultiplyBlocks : List (ℕ × ℕ) := [(23,1),(29,1),(35,1),(41,1),(42,35106),(35148,1)]

def compositions : Array Recipe := #[
  ⟨"close",false,11,292890196199,[(11,5),(16,5),(21,5),(26,5),(31,5),(36,5),(41,5),(46,5)],[⟨.library 13,[0,1,2,3,4,26,27,28,29,30],51,140654⟩,
    ⟨.library 13,[5,6,7,8,9,31,32,33,34,35],140705,140654⟩,
    ⟨.library 13,[11,12,13,14,15,36,37,38,39,40],281359,140654⟩,
    ⟨.library 13,[16,17,18,19,20,41,42,43,44,45],422013,140654⟩,
    ⟨.library 13,[21,22,23,24,25,46,47,48,49,50],562667,140654⟩,
    ⟨.recipe "precision",[26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50],703321,292889492836⟩,
    ⟨.library 15,[11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,10],292890196157,53⟩]⟩,
  ⟨"main",false,6,292890231486,[(6,5)],[⟨.recipe "close",[0,1,2,3,4,6,7,8,9,10,5],11,292890196199⟩,
    ⟨.library 16,[0,1,2,3,4,6,7,8,9,10,5],292890196210,35282⟩]⟩,
  ⟨"value_union",true,6,292890231892,[],[⟨.library 17,[0,1,2,3,4,5],6,406⟩,
    ⟨.recipe "main",[0,1,2,3,4,5],412,292890231486⟩]⟩,
  ⟨"value",false,6,292890231899,[],[⟨.library 0,[0,1,2,3,4],6,7⟩,
    ⟨.recipe "value_union",[0,1,2,3,4,5],13,292890231892⟩]⟩,
  ⟨"integers",false,1,292890231904,[(1,5)],[⟨.recipe "value",[1,2,3,4,5,0],6,292890231899⟩]⟩]

-- END DECODED RECORDS

/-- An invocation stands for the whole callee polynomial. The source row of the
invocation determines both its input registers and its witness offset. -/
inductive Term
  | var (index : ℕ)
  | int (value : ℤ)
  | add (left right : Term)
  | mul (left right : Term)
  | ell
  | invocation (row : ℕ)
  | missing (row : ℕ)
  deriving Inhabited, DecidableEq

private def reg (a : Array Term) (i : ℕ) := a[i]?.getD (.missing i)

private def expandGate (a : Array Term) : Gate → Term
  | .var i => .var i
  | .int c => .int c
  | .add i j => .add (reg a i) (reg a j)
  | .mul i j => .mul (reg a i) (reg a j)
  | .ell => .ell
  | .call _ _ _ => .invocation a.size

private def registers : Array Term :=
  multiplyNodes.foldl (fun a g => a.push (expandGate a g)) #[]

def multiplyOuterRoot : Term := reg registers 83

private def difference (x y : Term) : Term := .add x (.mul (.int (-1)) y)
private def squares (xs : List Term) : Term :=
  match xs.map (fun x => Term.mul x x) with
  | [] => .int 0
  | a :: as => as.foldl Term.add a

def globalDifferences : List Term :=
  [difference (.mul (.int 8) (.var 15)) (.int 1641),
   difference (.mul (.int 4) (.var 16)) (.int (-15465)),
   difference (.mul (.int 32) (.var 17)) (.int 87483)]

def invocationRows : List ℕ := [37,43,49,55,57,58]

/-- The square of the complete sum of six call squares occurs at node 80. The
three fixed-generator equations are conjoined outside that square. -/
theorem saved_multiply_formula :
    multiplyOuterRoot = squares (globalDifferences ++ [squares (invocationRows.map Term.invocation)]) := by
  decide +kernel

def recordedCalls : List (ℕ × ℕ × ℕ × ℕ) :=
  multiplyNodes.toList.zipIdx.filterMap fun
    | (.call id first args, row) => some (row,id,first,args.length)
    | _ => none

theorem saved_multiply_calls : recordedCalls =
    [(37,9,23,10),(43,9,29,10),(49,9,35,10),(55,9,41,10),(57,8,42,36),(58,10,35148,15)] := by
  decide +kernel

/-- Each of the 35,134 witnesses is either an explicit local variable or belongs
to exactly one private callee block. The four five-coordinate shifts are separate
from the four scalar-callee witnesses. -/
def multiplyRanges : List (ℕ × ℕ) :=
  [(15,3),(18,5),(23,1),(24,5),(29,1),(30,5),(35,1),(36,5),(41,1),(42,35106),(35148,1)]

theorem saved_multiply_allocation :
    explicitMultiplyIndices = [15,16,17,18,19,20,21,22,24,25,26,27,28,30,31,32,33,34,36,37,38,39,40] ∧
    recordedMultiplyBlocks = [(23,1),(29,1),(35,1),(41,1),(42,35106),(35148,1)] ∧
    multiplyRanges.head? = some (15,3) ∧
    (multiplyRanges.zip multiplyRanges.tail).all (fun t => t.1.1+t.1.2 == t.2.1) ∧
    (multiplyRanges.map Prod.snd).sum = 35134 ∧ 35148+1=15+35134 := by
  decide +kernel

theorem saved_root : compositions[4]? =
    some ⟨"integers",false,1,292890231904,[(1,5)],
      [⟨.recipe "value",[1,2,3,4,5,0],6,292890231899⟩]⟩ := by
  decide +kernel

theorem saved_value : compositions[3]? =
    some ⟨"value",false,6,292890231899,[],
      [⟨.library 0,[0,1,2,3,4],6,7⟩,⟨.recipe "value_union",[0,1,2,3,4,5],13,292890231892⟩]⟩ := by
  decide +kernel

/-- This interpretation substitutes values of the *six complete invocations*.
A binding to any concrete library supplies the values of its own callees. -/
def Term.eval (x : ℕ → ℚ) (e : ℚ) (c : ℕ → ℚ) : Term → ℚ
  | .var i => x i
  | .int z => z
  | .add a b => a.eval x e c + b.eval x e c
  | .mul a b => a.eval x e c * b.eval x e c
  | .ell => e
  | .invocation i => c i
  | .missing _ => 0

private theorem addSquare {z : ℚ} (h : 0≤z) (a : ℚ) :
    z+a*a=0 ↔ z=0 ∧ a=0 := by
  rw [add_eq_zero_iff_of_nonneg h (mul_self_nonneg a),mul_eq_zero,or_self]

private theorem four (a b c d : ℚ) :
    a*a+b*b+c*c+d*d=0 ↔ a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  rw [addSquare (by simp only [←pow_two]; positivity : 0≤a*a+b*b+c*c),addSquare (by simp only [←pow_two]; positivity : 0≤a*a+b*b),
    addSquare (mul_self_nonneg a)]
  simp only [mul_eq_zero,or_self,and_assoc]

private theorem six (a b c d e f : ℚ) :
    a*a+b*b+c*c+d*d+e*e+f*f=0 ↔ a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 := by
  rw [addSquare (by simp only [←pow_two]; positivity : 0≤a*a+b*b+c*c+d*d+e*e),addSquare (by simp only [←pow_two]; positivity : 0≤a*a+b*b+c*c+d*d),four]
  simp only [and_assoc]

theorem saved_multiply_outer_zero (x : ℕ → ℚ) (e : ℚ) (c : ℕ → ℚ) :
    multiplyOuterRoot.eval x e c = 0 ↔
      8*x 15=1641 ∧ 4*x 16= -15465 ∧ 32*x 17=87483 ∧
      c 37=0 ∧ c 43=0 ∧ c 49=0 ∧ c 55=0 ∧ c 57=0 ∧ c 58=0 := by
  rw [saved_multiply_formula]
  let a : ℚ := 8*x 15+(-1)*1641
  let b : ℚ := 4*x 16+(-1)*(-15465)
  let d : ℚ := 32*x 17+(-1)*87483
  let s := c 37*c 37+c 43*c 43+c 49*c 49+c 55*c 55+c 57*c 57+c 58*c 58
  change a*a+b*b+d*d+s*s=0 ↔ _
  rw [four,show s=0 ↔ _ from six (c 37) (c 43) (c 49) (c 55) (c 57) (c 58)]
  have eqv (v w : ℚ) : v+(-1)*w=0 ↔ v=w := by constructor <;> intro h <;> linarith
  exact and_congr (eqv _ _) (and_congr (eqv _ _) (and_congr_left' (eqv _ _)))

end ManuscriptV15.Saved
#print axioms ManuscriptV15.Saved.saved_multiply_formula
#print axioms ManuscriptV15.Saved.saved_multiply_calls
#print axioms ManuscriptV15.Saved.saved_multiply_allocation
#print axioms ManuscriptV15.Saved.saved_root
#print axioms ManuscriptV15.Saved.saved_value
#print axioms ManuscriptV15.Saved.saved_multiply_outer_zero
