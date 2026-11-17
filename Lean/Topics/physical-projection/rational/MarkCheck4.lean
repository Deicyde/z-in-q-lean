import MarkCheck3
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark20 (g : Bool) : (tail20 g).all markTest=true := by
  change (markTest p580 && (tail21 g).all markTest)=true
  rw [mark21];cases g <;> decide
theorem mark19 (g : Bool) : (tail19 g).all markTest=true := by
  change (markTest p581 && (tail20 g).all markTest)=true
  rw [mark20];cases g <;> decide
theorem mark18 (g : Bool) : (tail18 g).all markTest=true := by
  change (markTest p601 && (tail19 g).all markTest)=true
  rw [mark19];cases g <;> decide
theorem mark17 (g : Bool) : (tail17 g).all markTest=true := by
  change (markTest p133 && (tail18 g).all markTest)=true
  rw [mark18];cases g <;> decide
theorem mark16 (g : Bool) : (tail16 g).all markTest=true := by
  change (markTest p132 && (tail17 g).all markTest)=true
  rw [mark17];cases g <;> decide
theorem mark15 (g : Bool) : (tail15 g).all markTest=true := by
  change (markTest p598 && (tail16 g).all markTest)=true
  rw [mark16];cases g <;> decide
theorem mark14 (g : Bool) : (tail14 g).all markTest=true := by
  change (markTest p568 && (tail15 g).all markTest)=true
  rw [mark15];cases g <;> decide
theorem mark13 (g : Bool) : (tail13 g).all markTest=true := by
  change (markTest p569 && (tail14 g).all markTest)=true
  rw [mark14];cases g <;> decide
theorem mark12 (g : Bool) : (tail12 g).all markTest=true := by
  change (markTest p597 && (tail13 g).all markTest)=true
  rw [mark13];cases g <;> decide
theorem mark11 (g : Bool) : (tail11 g).all markTest=true := by
  change (markTest p314 && (tail12 g).all markTest)=true
  rw [mark12];cases g <;> decide
theorem mark10 (g : Bool) : (tail10 g).all markTest=true := by
  change (markTest p611 && (tail11 g).all markTest)=true
  rw [mark11];cases g <;> decide
theorem mark9 (g : Bool) : (tail9 g).all markTest=true := by
  change (markTest p588 && (tail10 g).all markTest)=true
  rw [mark10];cases g <;> decide
theorem mark8 (g : Bool) : (tail8 g).all markTest=true := by
  change (markTest p587 && (tail9 g).all markTest)=true
  rw [mark9];cases g <;> decide
end PhysicalProjection
