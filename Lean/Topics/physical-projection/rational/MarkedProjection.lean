import PhysicalProjection
import MarkCheck5
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

private def witness (i : Nat) : Rat := if i∈halfSlots then 1/2 else (integralValues i:Rat)
private def zpar : DBlock→Rat := fun _ => 0

def designated : Fin 130→Rat := candidate witness zpar

theorem designated_coordinates (i : Fin 130) :
    designated i = if (parentSlots[i.val]?).getD 0 ∈halfSlots then (1:Rat)/2 else 0 := by
  let j:=(parentSlots[i.val]?).getD 0
  have valid : i.val<parentSlots.length := by rw [parents_len]; exact i.isLt
  have mem : j∈parentSlots := by dsimp [j]; rw [List.getElem?_eq_getElem valid]; exact List.getElem_mem ..
  have values : parentSlots.all (fun n => decide (integralValues n=0))=true := by decide
  have zero : integralValues j=0 := of_decide_eq_true (List.all_eq_true.mp values j mem)
  change encoded witness zpar j = if j∈halfSlots then _ else _
  by_cases port : j∈ports
  · simp [ports] at port; rcases port with h|h|h <;> rw [h] <;> rfl
  · rw [encoded_keep port]; unfold witness; rw [zero]; rfl

private theorem witness_pivots (g : Bool) : pivotOK g witness := by
  have ints : (ps g).all (fun p => decide (intVal integralValues p.row=0))=true := mark0 g
  have free : (ps g).all (fun p => reads (apart halfSlots) p.row)=true := by cases g <;> decide
  intro p mem
  have val := of_decide_eq_true (List.all_eq_true.mp ints p mem)
  have offV : off halfSlots (fun i => (integralValues i:Rat)) witness := by intro i hi; simp [witness,hi]
  have same := agree_off offV p.row (reads_supported (List.all_eq_true.mp free p mem))
  apply (pivot_cell p.pre p.post p.slot p.lead witness).mp
  change value witness p.row=0
  rw [same,←int_value,val]; rfl

private theorem witness_parameters (k : DBlock) : fits k witness (zpar k) := by
  cases k <;> simp [fits,DBlock.e,DBlock.t,zpar,witness,halfSlots,integralValues,oneSlots] <;> grobner

private theorem witness_pade (k : PPair) : value witness k.f=0 ∧ value witness k.g=0 := by
  have vals (p : Polynomial) (v : intVal integralValues p=0) (away : reads (apart halfSlots) p=true) : value witness p=0 := by
    have offV : off halfSlots (fun i => (integralValues i:Rat)) witness := by intro i hi; simp [witness,hi]
    rw [agree_off offV p (reads_supported away),←int_value,v]; rfl
  cases k <;> exact ⟨vals _ (by decide) (by decide),vals _ (by decide) (by decide)⟩

private theorem witness_out (i : Nat) (hi : inside i=false) : witness i=0 := by
  have interior : halfSlots.all inside=true := by decide
  have miss : i∉halfSlots := by intro h; have insideVal:=List.all_eq_true.mp interior i h;rw [hi] at insideVal;contradiction
  have insideOnes : (178::179::oneSlots).all inside=true := by decide
  have none : i∉178::179::oneSlots := fun h => by have v:=List.all_eq_true.mp insideOnes i h;rw [hi] at v; contradiction
  simp at none
  simp [witness,miss,integralValues,none]

private theorem witness_peak (g : Bool) : rowsHold (peakRows g) witness := by
  have listed : peakRows g=[(335,p335),(385,p385),(435,p435)] := by cases g <;> rfl
  rw [listed];simp [rowsHold,p335,p385,p435,value,termValue,monomialValue,witness,halfSlots,integralValues,oneSlots]
  grobner

/-- Actual marked vector; the three half coordinates kill the three unreduced peak rows. -/
theorem designated_zero (g : Bool) : finiteLift designated 1=0 ∧ chart g true designated := by
  have agree:=chart_agrees g witness zpar (witness_pivots g) witness_parameters witness_pade witness_out
  have input : finiteLift designated 1=0 := by
    change designated ⟨0,by decide⟩=0
    rw [designated_coordinates];rfl
  refine ⟨input,?_,Or.inl input⟩
  intro r hr
  have active := (List.mem_filter.mp hr).1
  exact (agree_off agree _ (reads_supported (physical_active g r active))).trans (witness_peak g _ hr)

/-- Marking the distinguished input gives precisely the parent projection together with zero. -/
theorem marked_projection (g : Bool) (a : Rat) :
    (∃ y : Fin 130→Rat,finiteLift y 1=a ∧ chart g true y) ↔ RowsProject 226 (parentRows g) a ∨ a=0 := by
  constructor
  · rintro ⟨y,inp,_,alt⟩;rcases alt with zero|old
    · exact Or.inr (inp.symm.trans zero)
    · exact Or.inl ((ordinary_projection g a).mpr ⟨y,inp,old⟩)
  · rintro (old|rfl)
    · obtain ⟨y,inp,act,gu⟩ := (ordinary_projection g a).mp old
      exact ⟨y,inp,fun r h => act r (List.mem_filter.mp h).1,Or.inr ⟨act,gu⟩⟩
    · exact ⟨designated,designated_zero g⟩

theorem marked_polynomial (g : Bool) (a : Rat) :
    (∃ y : Fin 130→Rat,finiteLift y 1=a ∧ chart g true y) ↔
      (∃ x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (parentRows g))=0) ∨ a=0 := by
  rw [marked_projection,ordinary_polynomial,←ordinary_projection]

end PhysicalProjection
