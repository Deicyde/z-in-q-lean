import JointCells

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private theorem base_list : joint 2={(2,1,1),(2,1,7),(2,1,10),(2,1,70),(3,1,7),(5,10,7),(14,5,35),(21,10,7),(35,1,7),(210,1,1),(210,1,7),(210,1,10),(210,1,70)} := by decide

private theorem cell_25 : (( {(2,1,1),(2,1,7),(2,1,10),(2,1,70),(3,1,7),(5,10,7),(14,5,35),(21,10,7),(35,1,7),(210,1,1),(210,1,7),(210,1,10),(210,1,70)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 2 5 25 (by decide)))={(2,1,1),(14,5,35),(21,10,7)} := by decide

private theorem cell_13 : (( {(2,1,1),(14,5,35),(21,10,7)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 2 13 13 (by decide)))={(2,1,1),(14,5,35)} := by decide

private theorem cell_64 : (( {(2,1,1),(14,5,35)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 2 2 64 (by decide)))={(2,1,1)} := by decide

/-- The exhaustive local conditions when the C-row carries every large exceptional prime. -/
theorem remainingC {x:ℚ} (h:concentrated x 2) : triples 2 x∈( {(2,1,1)} : Finset (ℤ×ℤ×ℤ) ) := by
  have A:=joint_contains h
  rw [base_list] at A
  have H0:=Finset.mem_filter.mpr ⟨A,effective_filter x 2 5 25 (by decide) ⟨2,by decide⟩ (by decide)⟩
  rw [cell_25] at H0
  have H1:=Finset.mem_filter.mpr ⟨H0,effective_filter x 2 13 13 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_13] at H1
  have H2:=Finset.mem_filter.mpr ⟨H1,effective_filter x 2 2 64 (by decide) ⟨6,by decide⟩ (by decide)⟩
  rw [cell_64] at H2
  exact H2

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.remainingC
