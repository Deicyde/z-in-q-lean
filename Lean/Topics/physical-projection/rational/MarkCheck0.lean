import MarkValues
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark73 (g : Bool) : (tail73 g).all markTest=true := rfl
theorem mark72 (g : Bool) : (tail72 g).all markTest=true := by
  change (markTest p684 && (tail73 g).all markTest)=true
  rw [mark73];cases g <;> decide
theorem mark71 (g : Bool) : (tail71 g).all markTest=true := by
  change (markTest p683 && (tail72 g).all markTest)=true
  rw [mark72];cases g <;> decide
theorem mark70 (g : Bool) : (tail70 g).all markTest=true := by
  change (markTest p680 && (tail71 g).all markTest)=true
  rw [mark71];cases g <;> decide
theorem mark69 (g : Bool) : (tail69 g).all markTest=true := by
  change (markTest p679 && (tail70 g).all markTest)=true
  rw [mark70];cases g <;> decide
theorem mark68 (g : Bool) : (tail68 g).all markTest=true := by
  change (markTest p564 && (tail69 g).all markTest)=true
  rw [mark69];cases g <;> decide
theorem mark67 (g : Bool) : (tail67 g).all markTest=true := by
  change (markTest (if g then p560b else p560a) && (tail68 g).all markTest)=true
  rw [mark68];cases g <;> decide
theorem mark66 (g : Bool) : (tail66 g).all markTest=true := by
  change (markTest p453 && (tail67 g).all markTest)=true
  rw [mark67];cases g <;> decide
theorem mark65 (g : Bool) : (tail65 g).all markTest=true := by
  change (markTest p658 && (tail66 g).all markTest)=true
  rw [mark66];cases g <;> decide
theorem mark64 (g : Bool) : (tail64 g).all markTest=true := by
  change (markTest p656 && (tail65 g).all markTest)=true
  rw [mark65];cases g <;> decide
theorem mark63 (g : Bool) : (tail63 g).all markTest=true := by
  change (markTest p657 && (tail64 g).all markTest)=true
  rw [mark64];cases g <;> decide
theorem mark62 (g : Bool) : (tail62 g).all markTest=true := by
  change (markTest p648 && (tail63 g).all markTest)=true
  rw [mark63];cases g <;> decide
theorem mark61 (g : Bool) : (tail61 g).all markTest=true := by
  change (markTest p647 && (tail62 g).all markTest)=true
  rw [mark62];cases g <;> decide
theorem mark60 (g : Bool) : (tail60 g).all markTest=true := by
  change (markTest p646 && (tail61 g).all markTest)=true
  rw [mark61];cases g <;> decide
end PhysicalProjection
