import SLP

namespace StructuralReduction.Transport
open CircuitTransport

/-- Addition and multiplication in a hash-consed program may exchange their two inputs. -/
def corresponds (slots wires : Nat→Nat) : Op→Op→Prop
  | .var i,.var j => j=slots i
  | .int a,.int b => a=b
  | .add i j,.add a b | .mul i j,.mul a b =>
      (a=wires i ∧ b=wires j) ∨ (b=wires i ∧ a=wires j)
  | _,_ => False

def parents : Op→List Nat
  | .var _ | .int _ => []
  | .add i j | .mul i j => [i,j]

private theorem one (x y a b : Assignment) (s f : Nat→Nat) (u v : Op)
    (rel : corresponds s f u v) (coordinates : ∀ n,x n=y (s n))
    (ih : ∀ j∈parents u,a j=b (f j)) : u.value x a=v.value y b := by
  cases u <;> cases v <;> simp_all [corresponds,parents,Op.value] <;> grind

/-- A forward topological correspondence suffices on the ancestors of the retained equations. -/
theorem retained_rows (old new : List Op) (s f : Nat→Nat) (included : Nat→Prop)
    (pair : ∀ i,included i → ∃ u v,old[i]?=some u ∧ new[f i]?=some v ∧
      u.safe i ∧ v.safe (f i) ∧ corresponds s f u v ∧ ∀ j∈parents u,included j ∧ j<i)
    (x y : Assignment) (coordinates : ∀ n,x n=y (s n)) (i : Nat) (hi : included i) :
    valueAt old x i=valueAt new y (f i) := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    obtain ⟨u,v,hu,hv,su,sv,rel,hj⟩:=pair i hi
    rw [instruction hu su,instruction hv sv]
    exact one x y _ _ s f u v rel coordinates (fun j mem=>ih j (hj j mem).2 (hj j mem).1)

#print axioms retained_rows
end StructuralReduction.Transport
