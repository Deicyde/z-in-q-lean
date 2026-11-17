import SLP

namespace StructuralReduction.Output
open CircuitTransport

inductive Tree where
  | square (address wire : Nat)
  | add (address : Nat) (left right : Tree)

def Tree.top : Tree→Nat
  | .square n _ | .add n _ _ => n

def Tree.rows : Tree→List Nat
  | .square _ r => [r]
  | .add _ a b => a.rows++b.rows

def Tree.value (v : Assignment) : Tree→Rat
  | .square _ r => v r * v r
  | .add _ a b => a.value v+b.value v

def Tree.checked (lookup : Nat→Option Op) : Tree→Bool
  | .square i r => decide (r<i) && decide (lookup i = some (.mul r r))
  | .add i a b => a.checked lookup && b.checked lookup && decide (a.top<i ∧ b.top<i) &&
       decide (lookup i = some (.add a.top b.top))

private theorem nonneg (v : Assignment) (t : Tree) : 0≤t.value v := by
  induction t with
  | square a r =>
    change 0≤v r*v r
    by_cases h : 0≤v r
    · exact Rat.mul_nonneg h h
    · have neg : 0 ≤ -(v r) := by grind
      have positive:=Rat.mul_nonneg neg neg
      grind
  | add a l r hl hr => exact Rat.add_nonneg hl hr

theorem zero_iff (v : Assignment) (t : Tree) : t.value v=0 ↔ ∀ j∈t.rows,v j=0 := by
  induction t with
  | square a r => simp [Tree.value,Tree.rows,Rat.mul_eq_zero]
  | add a l r hl hr =>
    change l.value v+r.value v=0 ↔ _
    have ll:=nonneg v l
    have rr:=nonneg v r
    constructor
    · intro h j m
      have eq1 : l.value v=0 := by grind
      have eq2 : r.value v=0 := by grind
      exact (List.mem_append.mp m).elim (hl.mp eq1 j) (hr.mp eq2 j)
    · intro h
      rw [hl.mpr (fun j m=>h j (List.mem_append_left _ m)),hr.mpr (fun j m=>h j (List.mem_append_right _ m)),Rat.add_zero]

theorem checked_value (ops : List Op) (x : Assignment) (t : Tree) (look : Nat→Option Op)
    (agrees : ∀ i o,look i=some o → ops[i]?=some o) (h : t.checked look=true) :
    valueAt ops x t.top=t.value (valueAt ops x) := by
  induction t with
  | square i r =>
    simp only [Tree.checked,Bool.and_eq_true_iff,decide_eq_true_eq] at h
    exact instruction (agrees i _ h.2) ⟨h.1,h.1⟩ x
  | add i l r hl hr =>
    simp only [Tree.checked,Bool.and_eq_true_iff,decide_eq_true_eq] at h
    change valueAt ops x i= _ + _
    have step:=instruction (agrees i _ h.2) h.1.2 x
    change valueAt ops x i=valueAt ops x l.top+valueAt ops x r.top at step
    rw [step,hl h.1.1.1,hr h.1.1.2]

def wireList : List Nat := [1072,1038,984,883,113,782,677,513,489,463,459,455,451,
  1304,1428,1552,1676,1800,4100,4149,4273,4397,4521,4645,6910,6959,7083,7207,7331,7455,9720,9917]

private def addRows (i : Nat) (t : Tree) : List Nat→Tree
  | [] => t
  | r::rs => addRows (i+2) (.add (i+1) t (.square i r)) rs

def form := addRows 9919 (.square 9918 1072) wireList.tail

private def pairs (i previous : Nat) : List Nat→List Op
  | [] => []
  | r::rs => .mul r r :: .add previous i :: pairs (i+2) (i+1) rs

def suffix : List Op := [.mul 1072 1072] ++ pairs 9919 9918 wireList.tail ++ [.mul 0 9980]
def lookup (i : Nat) : Option Op := if i<9918 then none else suffix[i-9918]?

private theorem actual {pre : List Op} (h : pre.length=9918) {i : Nat} {op : Op}
    (ho : lookup i=some op) : (pre++suffix)[i]?=some op := by
  unfold lookup at ho
  split at ho
  · contradiction
  · rw [List.getElem?_append_right (by omega),h]
    exact ho

theorem signed_outputs (pre : List Op) (length : pre.length=9918) (input : pre[0]?=some (.var 1))
    (x : Assignment) :
    let v := valueAt (pre++suffix) x
    (v 9980=0 ↔ ∀ j∈wireList,v j=0) ∧ (v 9981=0 ↔ x 1=0 ∨ ∀ j∈wireList,v j=0) := by
  let ops := pre++suffix
  let v := valueAt ops x
  have h:=checked_value ops x form lookup (fun _ _=>actual length) (by decide)
  have top : form.top=9980 := by decide
  have rows : form.rows=wireList := by decide
  have ordinary : v 9980=0 ↔ ∀ j∈wireList,v j=0 := by
    rw [←rows,←zero_iff,←h,top]
  have m:=instruction (actual length (i:=9981) (op:=.mul 0 9980) (by decide)) (by decide) x
  have xx : ops[0]?=some (.var 1) := by
    unfold ops
    rwa [List.getElem?_append_left (by omega)]
  have xv:=instruction xx (by decide) x
  change v 0=x 1 at xv
  change v 9981=v 0*v 9980 at m
  exact ⟨ordinary,by change v 9981=0 ↔ _;rw [m,xv,Rat.mul_eq_zero,ordinary]⟩

#print axioms signed_outputs
end StructuralReduction.Output
