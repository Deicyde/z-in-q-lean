import TowerWidth

/-! The actual integer polynomial for the supplied finite tower.
The term stays compact because its resultant construction is not unfolded. -/
open ZInQBlueprint.SunResultant Sun28.Branches Sun28.Compiler
namespace WidthTower.Literal314
noncomputable section

private inductive Op where
  | integer (c : ℤ)
  | param (i : ℕ)
  | root (i : ℕ)
  | plus (a b : ℕ)
  | times (a b : ℕ)
deriving Inhabited

private def readOp (s : String) : Option Op := do
  match s.splitOn " " with
  | ["integer",c] => return .integer (← c.toInt?)
  | ["parameter",i] => return .param (← i.toNat?)
  | ["root",i] => return .root (← i.toNat?)
  | ["add",a,b] => return .plus (← a.toNat?) (← b.toNat?)
  | ["multiply",a,b] => return .times (← a.toNat?) (← b.toNat?)
  | _ => none

private def lines (s : String) := (s.splitOn "\n").filter (!·.isEmpty)
private def addresses (s : String) := (s.splitOn " ").mapM String.toNat?
private def ops : Array Op :=
  ((lines (include_str "data/nodes.txt")).mapM readOp).getD [] |>.toArray
private def stages : List (List ℕ) :=
  ((lines (include_str "data/stages.txt")).mapM addresses).getD []
private def tests : List (List ℕ) :=
  ((lines (include_str "data/right-sides.txt")).mapM addresses).getD []

-- These checks run when compiling the module and reject malformed source packets.
#guard ops.size == 9539
#guard stages.length == 232
#guard tests.map List.length == [294,232]

/-- At level n the most recently adjoined root has index zero in ParamTower. -/
private def registers (n : ℕ) : Array (Test 82 n) :=
  ops.foldl (fun reg op => reg.push (match op with
    | .integer c => (c : Test 82 n)
    | .param j => if h : j < 82 then MvPolynomial.C (MvPolynomial.X ⟨j,h⟩) else 0
    | .root j => if h : j < n then MvPolynomial.X ⟨n-1-j, by omega⟩ else 0
    | .plus a b => reg[a]! + reg[b]!
    | .times a b => reg[a]! * reg[b]!)) #[]

private def step {n : ℕ} (t : ParamTower (Poly 82) n) (ids : List ℕ) :
    ParamTower (Poly 82) (n+1) :=
  let values := registers n
  let coeff : Fin ids.length → Test 82 n := fun i => values[ids[i]]!
  let f := Polynomial.X ^ ids.length +
    ∑ i : Fin ids.length, Polynomial.C (coeff i) * Polynomial.X ^ (i : ℕ)
  .adjoin t f (Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt coeff))

private def pack : List (List ℕ) → Σ n, ParamTower (Poly 82) n
  | [] => ⟨0,.base⟩
  | a :: rest => let p := pack rest; ⟨p.1+1,step p.2 a⟩

private def family := pack stages.reverse
private def select (i : ℕ) : List (Test 82 family.1) :=
  (tests[i]!).map fun j => (registers family.1)[j]!

/-- Fixed before the rational input is supplied. Its arity includes the input. -/
def polynomial83 : Poly 83 :=
  inputPolynomial (n := 81) family.2 (select 0) (select 1)

def admits (x : ℚ) : Prop :=
  ∃ y : Fin 81 → ℚ, Solutions family.2 (select 0) (select 1) (Fin.cases x y)

theorem projection83 (x : ℚ) :
    (∃ w : Fin 82 → ℚ, value (Fin.cases x w) polynomial83 = 0) ↔ admits x :=
  input_projection family.2 (select 0) (select 1) x

end
end WidthTower.Literal314
#print axioms WidthTower.Literal314.projection83
