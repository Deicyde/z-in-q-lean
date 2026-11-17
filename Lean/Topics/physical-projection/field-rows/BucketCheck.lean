import SCurveFactors
namespace PhysicalProjection.FieldRows.Sparse
open ZeroInput.Sparse ProjectionDescent

def tag (m : List Nat) : Nat := m.foldl (fun s i => s + (if i=6 then 1 else if i=7 then 5 else if i=176 then 11 else if i=177 then 17 else i)) 0

def bit (n : Nat) (t : Term) : Bool := ((tag t.monomial)/2^n)%2==1


def branches (k : Nat) (p : Polynomial) : Nat→Bool
  | 0 => cert p []
  | n+1 => branches (k+1) (p.filter (bit k)) n && branches (k+1) (p.filter (fun t=> !bit k t)) n

private theorem split_value (p : Polynomial) (f : Term→Bool) (x : Assignment) :
    value x (p.filter f)+value x (p.filter fun t=> !f t)=value x p := by
  induction p with
  | nil=>simp [value,Rat.add_zero]
  | cons t p ih => cases h:f t <;> simp [h,value] <;> grobner

theorem branches_zero (k : Nat) (p : Polynomial) (n : Nat) (good : branches k p n=true) (x : Assignment) : value x p=0 := by
  induction n generalizing k p with
  | zero => exact sound good x
  | succ n ih =>
    obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp good
    rw [←split_value p (bit k) x,ih _ _ a,ih _ _ b];grobner

theorem subtract_zero (a b : Polynomial) (x : Assignment) (h : value x (ap a (sp (-1) b))=0) : value x a=value x b := by
  rw [at_a,at_s] at h;grobner
end PhysicalProjection.FieldRows.Sparse
