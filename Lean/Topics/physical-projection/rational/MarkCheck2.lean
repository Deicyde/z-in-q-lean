import MarkCheck1
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark46 (g : Bool) : (tail46 g).all markTest=true := by
  change (markTest p635 && (tail47 g).all markTest)=true
  rw [mark47];cases g <;> decide
theorem mark45 (g : Bool) : (tail45 g).all markTest=true := by
  change (markTest p626 && (tail46 g).all markTest)=true
  rw [mark46];cases g <;> decide
theorem mark44 (g : Bool) : (tail44 g).all markTest=true := by
  change (markTest p625 && (tail45 g).all markTest)=true
  rw [mark45];cases g <;> decide
theorem mark43 (g : Bool) : (tail43 g).all markTest=true := by
  change (markTest p624 && (tail44 g).all markTest)=true
  rw [mark44];cases g <;> decide
theorem mark42 (g : Bool) : (tail42 g).all markTest=true := by
  change (markTest p623 && (tail43 g).all markTest)=true
  rw [mark43];cases g <;> decide
theorem mark41 (g : Bool) : (tail41 g).all markTest=true := by
  change (markTest p620 && (tail42 g).all markTest)=true
  rw [mark42];cases g <;> decide
theorem mark40 (g : Bool) : (tail40 g).all markTest=true := by
  change (markTest p619 && (tail41 g).all markTest)=true
  rw [mark41];cases g <;> decide
theorem mark39 (g : Bool) : (tail39 g).all markTest=true := by
  change (markTest p364 && (tail40 g).all markTest)=true
  rw [mark40];cases g <;> decide
theorem mark38 (g : Bool) : (tail38 g).all markTest=true := by
  change (markTest p633 && (tail39 g).all markTest)=true
  rw [mark39];cases g <;> decide
theorem mark37 (g : Bool) : (tail37 g).all markTest=true := by
  change (markTest p632 && (tail38 g).all markTest)=true
  rw [mark38];cases g <;> decide
theorem mark36 (g : Bool) : (tail36 g).all markTest=true := by
  change (markTest p631 && (tail37 g).all markTest)=true
  rw [mark37];cases g <;> decide
theorem mark35 (g : Bool) : (tail35 g).all markTest=true := by
  change (markTest p350 && (tail36 g).all markTest)=true
  rw [mark36];cases g <;> decide
theorem mark34 (g : Bool) : (tail34 g).all markTest=true := by
  change (markTest p345 && (tail35 g).all markTest)=true
  rw [mark35];cases g <;> decide
end PhysicalProjection
