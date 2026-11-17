import JointCells

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private theorem base_list : joint 0={(1,1,1),(1,1,7),(1,1,10),(1,1,70),(5,5,35),(10,10,7)} := by decide

private theorem cell_49 : (( {(1,1,1),(1,1,7),(1,1,10),(1,1,70),(5,5,35),(10,10,7)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 0 7 49 (by decide)))={(1,1,1),(5,5,35),(10,10,7)} := by decide

private theorem cell_11 : (( {(1,1,1),(5,5,35),(10,10,7)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 0 11 11 (by decide)))={(1,1,1),(5,5,35)} := by decide

private theorem cell_64 : (( {(1,1,1),(5,5,35)} : Finset (ℤ×ℤ×ℤ) ).filter (compatible 0 2 64 (by decide)))={(1,1,1)} := by decide

/-- The exhaustive local conditions when the A-row carries every large exceptional prime. -/
theorem remainingA {x:ℚ} (h:concentrated x 0) : triples 0 x∈( {(1,1,1)} : Finset (ℤ×ℤ×ℤ) ) := by
  have A:=joint_contains h
  rw [base_list] at A
  have H0:=Finset.mem_filter.mpr ⟨A,effective_filter x 0 7 49 (by decide) ⟨2,by decide⟩ (by decide)⟩
  rw [cell_49] at H0
  have H1:=Finset.mem_filter.mpr ⟨H0,effective_filter x 0 11 11 (by decide) ⟨1,by decide⟩ (by decide)⟩
  rw [cell_11] at H1
  have H2:=Finset.mem_filter.mpr ⟨H1,effective_filter x 0 2 64 (by decide) ⟨6,by decide⟩ (by decide)⟩
  rw [cell_64] at H2
  exact H2

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.remainingA
