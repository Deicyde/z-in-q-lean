import SLP
import PhysicalScalar

namespace StructuralReduction.Wires

/-- Both evaluators have the same four integer instruction constructors. -/
def fromCircuit : CircuitTransport.Op → Op
  | .var k => .var k
  | .int c => .int c
  | .add a b => .add a b
  | .mul a b => .mul a b

def arguments : CircuitTransport.Op → List Nat
  | .var _ | .int _ => []
  | .add a b | .mul a b => [a,b]

/-- Agreement on any backward-closed set of physical addresses identifies the full
array evaluator of the released integer programs with the local scalar evaluator. -/
theorem valueAt_read (ops : List CircuitTransport.Op) (g : Nat→Op) (x : Nat→Rat)
    (included : Nat→Prop)
    (bind : ∀i,included i → ∃o,ops[i]?=some o ∧ o.safe i ∧ complete g i=fromCircuit o ∧
        ∀j∈arguments o,included j)
    (i : Nat) (hi : included i) : CircuitTransport.valueAt ops x i=read (complete g) x i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    obtain ⟨o,look,safe,e,closed⟩:=bind i hi
    rw [CircuitTransport.instruction look safe x]
    cases o with
    | var k => exact (read_var _ _ e).symm
    | int c => exact (read_int _ _ e).symm
    | add a b =>
      change CircuitTransport.valueAt ops x a+CircuitTransport.valueAt ops x b=_
      rw [read_add _ _ e safe.1 safe.2,ih a safe.1 (closed a (by simp [arguments])),
          ih b safe.2 (closed b (by simp [arguments]))]
    | mul a b =>
      change CircuitTransport.valueAt ops x a*CircuitTransport.valueAt ops x b=_
      rw [read_mul _ _ e safe.1 safe.2,ih a safe.1 (closed a (by simp [arguments])),
          ih b safe.2 (closed b (by simp [arguments]))]

end StructuralReduction.Wires
