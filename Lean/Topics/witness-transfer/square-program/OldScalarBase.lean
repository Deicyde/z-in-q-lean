import SquareData
namespace SquareProgram.OldScalar
open CircuitTransport IndependentIndices Data
def scalarRegion (i : Nat) : Prop := i=0 ∨ i=131 ∨ i=132 ∨ i=135 ∨ (21493≤i ∧ i≤21567)
instance (i : Nat) : Decidable (scalarRegion i) := by unfold scalarRegion;infer_instance

private theorem non_witness_nodes :
    (peaks++others).all (fun r=>match r with | .replace492=>true | .inherit _ n _=>decide (¬scalarRegion n))=true := by
  decide +kernel

theorem fixed_op {i : Nat} {o : Op} (hi : i<21887) (hs : scalarRegion i) (fixed : ScalarSource.lookup i=some o) :
    source[i]?=some o := by
  rw [source_spec]
  apply untouched
  · intro f n p mem eq
    have h:=List.all_eq_true.mp non_witness_nodes (.inherit f n p) mem
    have no : ¬scalarRegion n := of_decide_eq_true h
    exact no (eq.symm ▸ hs)
  · rw [original_spec]
    dsimp only [ScalarSource.raw]
    rw [List.getElem?_map,List.getElem?_range hi]
    simp [fixed]
end SquareProgram.OldScalar
