import SLP

namespace ProjectionFibres
open CircuitTransport

/-- Classes 0, 1 and 2 allow successively more input coordinates.
A result has at least the class of every operand it reads. -/
def allowed (slots wires : Nat → Nat) (i : Nat) : Op → Bool
  | .var k => decide (slots k ≤ wires i)
  | .int _ => true
  | .add a b | .mul a b => decide (a<i ∧ b<i ∧ wires a≤wires i ∧ wires b≤wires i)

def slotClass (i : Nat) : Nat :=
  if i=21 ∨ i=22 then 1 else if i=27 ∨ i=28 ∨ i=29 ∨ i=84 then 2 else 0

theorem unchanged {ops : List Op} {limit : Nat} (select : Nat → Op) (slots wires : Nat → Nat) (cut : Nat→Bool)
    (entry : ∀ i<limit,ops[i]?=some (select i))
    (verified : ∀ i<limit,cut i=false → allowed slots wires i (select i)=true)
    (level : Nat) {x y : Assignment} (agree : ∀ k,slots k≤level → x k=y k)
    (known : ∀i<limit, cut i=true → valueAt ops x i=valueAt ops y i)
    (i : Nat) (bound : i<limit) (live : wires i≤level) :
    valueAt ops x i=valueAt ops y i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have e:=entry i bound
    by_cases inside : cut i=true
    · exact known i bound inside
    have check:=verified i bound (by simpa using inside)
    cases h : select i with
    | var n =>
      rw [h] at e check
      rw [instruction e trivial x,instruction e trivial y]
      exact agree n (Nat.le_trans (of_decide_eq_true check) live)
    | int c =>
      rw [h] at e
      rw [instruction e trivial x,instruction e trivial y]
      rfl
    | add a b =>
      rw [h] at e check
      obtain ⟨ha,hb,ca,cb⟩ := of_decide_eq_true check
      have ea:=ih a ha (Nat.lt_trans ha bound) (Nat.le_trans ca live)
      have eb:=ih b hb (Nat.lt_trans hb bound) (Nat.le_trans cb live)
      simp only [instruction e ⟨ha,hb⟩ x,instruction e ⟨ha,hb⟩ y,Op.value,ea,eb]
    | mul a b =>
      rw [h] at e check
      obtain ⟨ha,hb,ca,cb⟩ := of_decide_eq_true check
      have ea:=ih a ha (Nat.lt_trans ha bound) (Nat.le_trans ca live)
      have eb:=ih b hb (Nat.lt_trans hb bound) (Nat.le_trans cb live)
      simp only [instruction e ⟨ha,hb⟩ x,instruction e ⟨ha,hb⟩ y,Op.value,ea,eb]

theorem of_blocks {p : Nat→Bool} {a n : Nat}
    (ok : (List.range n).all (fun j=>p (a+j))=true) {i : Nat}
    (lo : a≤i) (hi : i<a+n) : p i=true := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lo
  exact List.all_eq_true.mp ok j (List.mem_range.mpr (by omega))

end ProjectionFibres
