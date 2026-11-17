import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal188 (g : Bool) (z : Assignment) : value z (literal g .S .output false) = rowScale .S .output false * component false (formula g .S .output z) := by
  have small (v : Assignment) : value v small188=3*(rowScale .S .output false * component false (plain g .S .output v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small188] <;> grobner
  have e:=congrArg (value z) data188
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p188=rowScale .S .output false * component false (plain g .S .output (shifted z))
  grobner
end PhysicalProjection.FieldRows
