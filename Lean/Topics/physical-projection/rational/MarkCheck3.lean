import MarkCheck2
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark33 (g : Bool) : (tail33 g).all markTest=true := by
  change (markTest p295 && (tail34 g).all markTest)=true
  rw [mark34];cases g <;> decide
theorem mark32 (g : Bool) : (tail32 g).all markTest=true := by
  change (markTest p292 && (tail33 g).all markTest)=true
  rw [mark33];cases g <;> decide
theorem mark31 (g : Bool) : (tail31 g).all markTest=true := by
  change (markTest p291 && (tail32 g).all markTest)=true
  rw [mark32];cases g <;> decide
theorem mark30 (g : Bool) : (tail30 g).all markTest=true := by
  change (markTest p614 && (tail31 g).all markTest)=true
  rw [mark31];cases g <;> decide
theorem mark29 (g : Bool) : (tail29 g).all markTest=true := by
  change (markTest p612 && (tail30 g).all markTest)=true
  rw [mark30];cases g <;> decide
theorem mark28 (g : Bool) : (tail28 g).all markTest=true := by
  change (markTest p613 && (tail29 g).all markTest)=true
  rw [mark29];cases g <;> decide
theorem mark27 (g : Bool) : (tail27 g).all markTest=true := by
  change (markTest p586 && (tail28 g).all markTest)=true
  rw [mark28];cases g <;> decide
theorem mark26 (g : Bool) : (tail26 g).all markTest=true := by
  change (markTest p585 && (tail27 g).all markTest)=true
  rw [mark27];cases g <;> decide
theorem mark25 (g : Bool) : (tail25 g).all markTest=true := by
  change (markTest p604 && (tail26 g).all markTest)=true
  rw [mark26];cases g <;> decide
theorem mark24 (g : Bool) : (tail24 g).all markTest=true := by
  change (markTest p603 && (tail25 g).all markTest)=true
  rw [mark25];cases g <;> decide
theorem mark23 (g : Bool) : (tail23 g).all markTest=true := by
  change (markTest p151 && (tail24 g).all markTest)=true
  rw [mark24];cases g <;> decide
theorem mark22 (g : Bool) : (tail22 g).all markTest=true := by
  change (markTest p150 && (tail23 g).all markTest)=true
  rw [mark23];cases g <;> decide
theorem mark21 (g : Bool) : (tail21 g).all markTest=true := by
  change (markTest p602 && (tail22 g).all markTest)=true
  rw [mark22];cases g <;> decide
end PhysicalProjection
