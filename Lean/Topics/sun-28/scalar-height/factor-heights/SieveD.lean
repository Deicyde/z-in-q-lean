import JointCells

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private theorem base_list : joint 3={(2,1,1),(3,1,1),(5,2,2),(5,10,10),(14,5,5),(21,10,10),(35,1,1),(35,5,5),(210,1,1)} := by decide

private theorem cell_25 : (( {(2,1,1),(3,1,1),(5,2,2),(5,10,10),(14,5,5),(21,10,10),(35,1,1),(35,5,5),(210,1,1)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 3 5 25 (by decide)))={(2,1,1),(3,1,1),(5,2,2),(14,5,5),(21,10,10)} := by decide

private theorem cell_49 : (( {(2,1,1),(3,1,1),(5,2,2),(14,5,5),(21,10,10)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 3 7 49 (by decide)))={(2,1,1),(14,5,5),(21,10,10)} := by decide

private theorem cell_11 : (( {(2,1,1),(14,5,5),(21,10,10)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 3 11 11 (by decide)))={(2,1,1),(14,5,5)} := by decide

private theorem cell_23 : (( {(2,1,1),(14,5,5)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 3 23 23 (by decide)))={(2,1,1)} := by decide

/-- The exhaustive local conditions when the D-row carries every large exceptional prime. -/
theorem remainingD {x:ℚ} (h:concentrated x 3) : triples 3 x∈( {(2,1,1)} : Finset (ℤ×ℤ×ℤ) ) := by
  have A:=joint_contains h
  rw [base_list] at A
  have H0:=Finset.mem_filter.mpr ⟨A,effective_filter x 3 5 25 (by decide) ⟨2,by decide⟩ (by decide)⟩
  rw [cell_25] at H0
  have H1:=Finset.mem_filter.mpr ⟨H0,effective_filter x 3 7 49 (by decide) ⟨2,by decide⟩ (by decide)⟩
  rw [cell_49] at H1
  have H2:=Finset.mem_filter.mpr ⟨H1,effective_filter x 3 11 11 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_11] at H2
  have H3:=Finset.mem_filter.mpr ⟨H2,effective_filter x 3 23 23 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_23] at H3
  exact H3

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.remainingD
