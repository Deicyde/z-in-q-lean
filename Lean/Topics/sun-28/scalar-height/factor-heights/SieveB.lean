import JointCells

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private theorem base_list : joint 1={(2,-7,2),(2,-7,5),(2,-7,14),(2,-7,35),(2,1,1),(2,1,7),(2,1,10),(2,1,70),(3,-35,7),(3,1,7),(5,-14,7),(5,10,7),(14,-35,7),(14,5,35),(21,-14,7),(21,10,7),(30,-35,7),(35,-35,7),(35,1,7),(210,1,1),(210,1,7),(210,1,10),(210,1,70)} := by decide

private theorem cell_25 : (( {(2,-7,2),(2,-7,5),(2,-7,14),(2,-7,35),(2,1,1),(2,1,7),(2,1,10),(2,1,70),(3,-35,7),(3,1,7),(5,-14,7),(5,10,7),(14,-35,7),(14,5,35),(21,-14,7),(21,10,7),(30,-35,7),(35,-35,7),(35,1,7),(210,1,1),(210,1,7),(210,1,10),(210,1,70)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 1 5 25 (by decide)))={(2,-7,2),(2,1,1),(14,-35,7),(14,5,35),(21,-14,7),(21,10,7)} := by decide

private theorem cell_11 : (( {(2,-7,2),(2,1,1),(14,-35,7),(14,5,35),(21,-14,7),(21,10,7)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 1 11 11 (by decide)))={(2,-7,2),(2,1,1),(14,-35,7),(14,5,35)} := by decide

private theorem cell_13 : (( {(2,-7,2),(2,1,1),(14,-35,7),(14,5,35)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 1 13 13 (by decide)))={(2,1,1),(14,-35,7),(14,5,35)} := by decide

private theorem cell_43 : (( {(2,1,1),(14,-35,7),(14,5,35)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 1 43 43 (by decide)))={(2,1,1),(14,-35,7)} := by decide

/-- The exhaustive local conditions when the B-row carries every large exceptional prime. -/
theorem remainingB {x:ℚ} (h:concentrated x 1) : triples 1 x∈( {(2,1,1),(14,-35,7)} : Finset (ℤ×ℤ×ℤ) ) := by
  have A:=joint_contains h
  rw [base_list] at A
  have H0:=Finset.mem_filter.mpr ⟨A,effective_filter x 1 5 25 (by decide) ⟨2,by decide⟩ (by decide)⟩
  rw [cell_25] at H0
  have H1:=Finset.mem_filter.mpr ⟨H0,effective_filter x 1 11 11 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_11] at H1
  have H2:=Finset.mem_filter.mpr ⟨H1,effective_filter x 1 13 13 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_13] at H2
  have H3:=Finset.mem_filter.mpr ⟨H2,effective_filter x 1 43 43 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_43] at H3
  exact H3

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.remainingB
