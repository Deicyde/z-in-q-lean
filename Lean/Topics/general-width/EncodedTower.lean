import RelativeWidth

/-! Read the integer coefficient circuit of a triangular system with equations and
inequations. Root addresses count from the earliest stage in the input files. -/
open ZInQBlueprint.SunResultant Sun28.Branches Sun28.Compiler
namespace EncodedTower
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
private def numbers (s : String) := (s.splitOn " ").mapM String.toNat?
structure Data where
  private ops : Array Op
  private stages : List (List ℕ)
  private tests : List (List ℕ)

def decode (nodes stages tests : String) : Data :=
  ⟨((lines nodes).mapM readOp).getD [] |>.toArray,
   ((lines stages).mapM numbers).getD [], ((lines tests).mapM numbers).getD []⟩

private def levels (b : Data) (m stages : ℕ) : Option (Array ℕ) :=
  b.ops.foldlM (fun (r : Array ℕ) op => do
    let v : ℕ ← match op with
      | .integer _ => pure 0
      | .param j => if j < m then pure 0 else none
      | .root j => if j < stages then pure (j+1) else none
      | .plus a b | .times a b => (max <$> r[a]? <*> r[b]?)
    return r.push v) #[]

/-- Check all addresses, root dependencies, stage degrees and list lengths. -/
def valid (b : Data) (m degreeCount nodeCount equationCount : ℕ) : Bool := Id.run do
  let some ℓ := levels b m degreeCount | return false
  let [eqs,guards] := b.tests | return false
  return b.ops.size == nodeCount && b.stages.length == degreeCount && eqs.length == equationCount &&
    guards.length == degreeCount && eqs.all (· < b.ops.size) &&
    (b.stages.zip guards).zipIdx.all fun ((coeff,guard),i) =>
      [1,2,4].contains coeff.length && (guard :: coeff).all (fun j =>
        (ℓ[j]?).any (· ≤ i))

private def registers (b : Data) (m n : ℕ) : Array (Test m n) :=
  b.ops.foldl (fun r op => r.push (match op with
    | .integer c => (c : Test m n)
    | .param j => if h : j < m then MvPolynomial.C (MvPolynomial.X ⟨j,h⟩) else 0
    | .root j => if h : j < n then MvPolynomial.X ⟨n-1-j, by omega⟩ else 0
    | .plus a b => r[a]! + r[b]!
    | .times a b => r[a]! * r[b]!)) #[]

private def step (b : Data) {m n : ℕ} (t : ParamTower (Poly m) n) (ids : List ℕ) :
    ParamTower (Poly m) (n+1) :=
  let values := registers b m n
  let coeff : Fin ids.length → Test m n := fun i => values[ids[i]]!
  let f := Polynomial.X ^ ids.length +
    ∑ i : Fin ids.length, Polynomial.C (coeff i) * Polynomial.X ^ (i : ℕ)
  .adjoin t f (Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt coeff))

private def pack (b : Data) (m : ℕ) : List (List ℕ) → Σ n, ParamTower (Poly m) n
  | [] => ⟨0,.base⟩
  | c :: cs => let p := pack b m cs; ⟨p.1+1, step b p.2 c⟩

def asBranch (b : Data) (m : ℕ) : RelativeWidth.TowerBranch m :=
  let t := pack b m b.stages.reverse
  let polys := registers b m t.1
  let select := fun (i : ℕ) => b.tests[i]!.map fun j => polys[j]!
  ⟨t.1,t.2,select 0,select 1⟩

end
end EncodedTower
