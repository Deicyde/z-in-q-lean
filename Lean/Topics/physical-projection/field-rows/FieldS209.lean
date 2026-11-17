import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal209 (g : Bool) (z : Assignment) : value z (literal g .S .iSquare false) = rowScale .S .iSquare false * component false (formula g .S .iSquare z) := by
  have small (v : Assignment) : value v small209=3*(rowScale .S .iSquare false * component false (plain g .S .iSquare v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small209] <;> grobner
  have e:=congrArg (value z) data209
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p209=rowScale .S .iSquare false * component false (plain g .S .iSquare (shifted z))
  grobner
end PhysicalProjection.FieldRows
