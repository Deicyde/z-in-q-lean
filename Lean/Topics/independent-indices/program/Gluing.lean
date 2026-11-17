import IndexTheorems

namespace IndependentIndices
open CircuitTransport

def owner (i : Nat) : Frame :=
  if i≤17 then .common else if i≤52 then .first else if i≤87 then .second
  else if i≤122 then .third else .scalar

def glue (inputs : Frame→Fin 134→Rat) (i : Fin 134) : Rat := inputs (owner (i.val+1)) i

private theorem inside (f : Frame) (i : Nat) (h : inFrame f i=true) : 1≤i ∧ i≤134 := by
  cases f <;> simp [inFrame] at h <;> omega

private theorem own_of_private (f : Frame) (i : Nat) (h : inFrame f i=true) (privateSlot : 17<i) :
    owner i=f := by
  cases f <;> simp [inFrame] at h
  all_goals unfold owner
  all_goals repeat' split
  all_goals first | rfl | omega

/-- Rational local assignments can be glued if their 17 common coordinates agree.
    The proof permits independently chosen values of every private frame coordinate. -/
theorem glue_solutions (g marked : Bool) (inputs : Frame→Fin 134→Rat)
    (common : ∀f i,i.val<17 → inputs f i=inputs .common i)
    (localRows : ∀f,holds g marked (inputs f) f) :
    (splitProgram g).eval marked (vector (glue inputs))=0 := by
  have agree (f : Frame) (j : Nat) (hj : inFrame f j=true) :
      vector (glue inputs) j=vector (inputs f) j := by
    have ip:=inside f j hj
    have valid : 0<j ∧ j≤134 := by omega
    simp only [vector,dif_pos valid,glue,show j-1+1=j by omega]
    by_cases share : j≤17
    · rw [show owner j=.common by simp [owner,share]]
      exact (common f _ (by simp;omega)).symm
    · rw [own_of_private f j hj (by omega)]
  have accepted (f : Frame) := (frame_congr g marked f _ _ (agree f)).mpr (localRows f)
  exact (split_iff g marked _).mpr ⟨accepted .common,accepted .first,accepted .second,accepted .third,accepted .scalar⟩

end IndependentIndices
