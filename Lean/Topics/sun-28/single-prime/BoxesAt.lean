import WidthSelection

namespace Sun28.SinglePrime
open Filter Sun28.WeightedSelection
noncomputable section

/-- Every single numerical rectangle occurs in a family of growing short boxes.
This lets finite inequalities apply also to individual members of a fixed aspect row. -/
theorem boxes_at (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (N W : ℕ) :
    ∃ boxes : CountingBoxes A d H Y,boxes.width N=W ∧ boxes.records N=box N W := by
  obtain ⟨s,_,_,g,short⟩:=choose_width (fun _=>0) (fun _ _=>True)
    (fun _=>Eventually.of_forall fun _=>Nat.zero_le _) (fun _=>Eventually.of_forall fun _=>trivial)
  let w b := if b=N then W else rowWidth (s b) b
  have changeAt : ∀ᶠ b : ℕ in atTop,w b=rowWidth (s b) b := by
    filter_upwards [eventually_gt_atTop N] with b hb
    simp [w,hb.ne']
  have grows : Tendsto w atTop atTop := g.congr' (changeAt.mono (fun b hb=>hb.symm))
  have small (ε : ℝ) (ep : 0<ε) : ∀ᶠ b : ℕ in atTop,(w b:ℝ)^2≤ε*b := by
    filter_upwards [short ε ep,changeAt] with b hb eq; rwa [eq]
  let boxes : CountingBoxes A d H Y := numericalBoxes w (fun j=>eventually_atTop.mp (tendsto_atTop.mp grows j))
    (fun ε ep=>eventually_atTop.mp (small ε ep))
  have eq : w N=W := by simp [w]
  exact ⟨boxes,eq,congrArg (box (A:=A) (d:=d) (H:=H) (Y:=Y) N) eq⟩
end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.boxes_at
