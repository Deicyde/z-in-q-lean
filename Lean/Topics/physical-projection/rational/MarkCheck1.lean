import MarkCheck0
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem mark59 (g : Bool) : (tail59 g).all markTest=true := by
  change (markTest p645 && (tail60 g).all markTest)=true
  rw [mark60];cases g <;> decide
theorem mark58 (g : Bool) : (tail58 g).all markTest=true := by
  change (markTest p642 && (tail59 g).all markTest)=true
  rw [mark59];cases g <;> decide
theorem mark57 (g : Bool) : (tail57 g).all markTest=true := by
  change (markTest p641 && (tail58 g).all markTest)=true
  rw [mark58];cases g <;> decide
theorem mark56 (g : Bool) : (tail56 g).all markTest=true := by
  change (markTest p414 && (tail57 g).all markTest)=true
  rw [mark57];cases g <;> decide
theorem mark55 (g : Bool) : (tail55 g).all markTest=true := by
  change (markTest p655 && (tail56 g).all markTest)=true
  rw [mark56];cases g <;> decide
theorem mark54 (g : Bool) : (tail54 g).all markTest=true := by
  change (markTest p654 && (tail55 g).all markTest)=true
  rw [mark55];cases g <;> decide
theorem mark53 (g : Bool) : (tail53 g).all markTest=true := by
  change (markTest p653 && (tail54 g).all markTest)=true
  rw [mark54];cases g <;> decide
theorem mark52 (g : Bool) : (tail52 g).all markTest=true := by
  change (markTest p399 && (tail53 g).all markTest)=true
  rw [mark53];cases g <;> decide
theorem mark51 (g : Bool) : (tail51 g).all markTest=true := by
  change (markTest p395 && (tail52 g).all markTest)=true
  rw [mark52];cases g <;> decide
theorem mark50 (g : Bool) : (tail50 g).all markTest=true := by
  change (markTest p297 && (tail51 g).all markTest)=true
  rw [mark51];cases g <;> decide
theorem mark49 (g : Bool) : (tail49 g).all markTest=true := by
  change (markTest p296 && (tail50 g).all markTest)=true
  rw [mark50];cases g <;> decide
theorem mark48 (g : Bool) : (tail48 g).all markTest=true := by
  change (markTest p636 && (tail49 g).all markTest)=true
  rw [mark49];cases g <;> decide
theorem mark47 (g : Bool) : (tail47 g).all markTest=true := by
  change (markTest p634 && (tail48 g).all markTest)=true
  rw [mark48];cases g <;> decide
end PhysicalProjection
