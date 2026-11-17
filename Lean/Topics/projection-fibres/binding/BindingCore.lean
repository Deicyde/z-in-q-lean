import SLP

namespace ProjectionFibres.Binding
open CircuitTransport

/-- A source variable is either a fixed child input or one of the two rescaled
inputs. A bound of zero isolates the base on which the guard depends. -/
def slotLevel (k : Nat) : Nat := if k=21 ∨ k=22 then 1 else 0

def retainedSlot (k : Nat) : Bool := decide (0<k ∧ k≤83 ∧ k≠27 ∧ k≠28 ∧ k≠29)

def binaryOK (op : Nat→Nat→Op) (level address : Nat→Nat) (i j k : Nat) (dst : Op) : Bool :=
  decide (j<i ∧ k<i ∧ level j≤level i ∧ level k≤level i ∧
    address j<address i ∧ address k<address i ∧
    (dst=op (address j) (address k) ∨ dst=op (address k) (address j)))

def checked (src dst : Nat→Op) (level address leaf : Nat→Nat) (limit i : Nat) : Bool :=
  if level i>1 then true else decide (address i<limit) && match src i with
  | .var k => retainedSlot k && decide (slotLevel k≤level i ∧ address i=leaf k)
  | .int c => decide (dst (address i)=.int c)
  | .add j k => binaryOK .add level address i j k (dst (address i))
  | .mul j k => binaryOK .mul level address i j k (dst (address i))

/-- Local gate checks on a closed dependency set imply equality of its two
array evaluators for every rational assignment satisfying the variable equations. -/
theorem map_value {old new : List Op} {src dst : Nat→Op} {level address leaf : Nat→Nat}
    {bound size : Nat} (left : ∀ i<bound,old[i]?=some (src i))
    (right : ∀ i<size,new[i]?=some (dst i))
    (ok : ∀ i<bound,checked src dst level address leaf size i=true)
    (x y : Assignment) {mode : Nat} (small : mode≤1)
    (vars : ∀k,retainedSlot k=true → slotLevel k≤mode → x k=valueAt new y (leaf k))
    (i : Nat) (inside : i<bound) (keep : level i≤mode) :
    valueAt old x i=valueAt new y (address i) := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have test:=ok i inside
    have e:=left i inside
    rw [checked,if_neg (by omega)] at test
    obtain ⟨out,test⟩:=Bool.and_eq_true_iff.mp test
    have f:=right (address i) (of_decide_eq_true out)
    cases s : src i with
    | var k =>
      rw [s] at e test
      obtain ⟨available,route⟩:=Bool.and_eq_true_iff.mp test
      obtain ⟨height,pos⟩:=of_decide_eq_true route
      rw [instruction e trivial x,pos]
      exact vars k available (by omega)
    | int c =>
      rw [s] at e test
      rw [of_decide_eq_true test] at f
      rw [instruction e trivial x,instruction f trivial y]
      rfl
    | add j k =>
      rw [s] at e test
      obtain ⟨ji,ki,jl,kl,da,db,way⟩:=of_decide_eq_true test
      have ej:=ih j ji (by omega) (by omega)
      have ek:=ih k ki (by omega) (by omega)
      rw [instruction e ⟨ji,ki⟩ x]
      rcases way with forward|backward
      · rw [forward] at f
        simp only [Op.value,instruction f ⟨da,db⟩ y,ej,ek]
      · rw [backward] at f
        simpa only [Op.value,instruction f ⟨db,da⟩ y,ej,ek] using
          Rat.add_comm (valueAt new y (address j)) (valueAt new y (address k))
    | mul j k =>
      rw [s] at e test
      obtain ⟨ji,ki,jl,kl,da,db,way⟩:=of_decide_eq_true test
      have ej:=ih j ji (by omega) (by omega)
      have ek:=ih k ki (by omega) (by omega)
      rw [instruction e ⟨ji,ki⟩ x]
      rcases way with forward|backward
      · rw [forward] at f
        simp only [Op.value,instruction f ⟨da,db⟩ y,ej,ek]
      · rw [backward] at f
        simpa only [Op.value,instruction f ⟨db,da⟩ y,ej,ek] using
          Rat.mul_comm (valueAt new y (address j)) (valueAt new y (address k))

end ProjectionFibres.Binding
