import MarkCheck4
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark7 (g : Bool) : (tail7 g).all markTest=true := by
  change (markTest p610 && (tail8 g).all markTest)=true
  rw [mark8];cases g <;> decide
theorem mark6 (g : Bool) : (tail6 g).all markTest=true := by
  change (markTest p609 && (tail7 g).all markTest)=true
  rw [mark7];cases g <;> decide
theorem mark5 (g : Bool) : (tail5 g).all markTest=true := by
  change (markTest p592 && (tail6 g).all markTest)=true
  rw [mark6];cases g <;> decide
theorem mark4 (g : Bool) : (tail4 g).all markTest=true := by
  change (markTest p590 && (tail5 g).all markTest)=true
  rw [mark5];cases g <;> decide
theorem mark3 (g : Bool) : (tail3 g).all markTest=true := by
  change (markTest p511 && (tail4 g).all markTest)=true
  rw [mark4];cases g <;> decide
theorem mark2 (g : Bool) : (tail2 g).all markTest=true := by
  change (markTest p591 && (tail3 g).all markTest)=true
  rw [mark3];cases g <;> decide
theorem mark1 (g : Bool) : (tail1 g).all markTest=true := by
  change (markTest p206 && (tail2 g).all markTest)=true
  rw [mark2];cases g <;> decide
theorem mark0 (g : Bool) : (tail0 g).all markTest=true := by
  change (markTest p205 && (tail1 g).all markTest)=true
  rw [mark1];cases g <;> decide
end PhysicalProjection
