import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal715 (g : Bool) (z : Assignment) : value z (literal g .S .quartic true) = rowScale .S .quartic true * component true (formula g .S .quartic z) := by
  have small (v : Assignment) : value v small715=3*(rowScale .S .quartic true * component true (plain g .S .quartic v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small715] <;> grobner
  have e:=congrArg (value z) data715
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p715=rowScale .S .quartic true * component true (plain g .S .quartic (shifted z))
  grobner
end PhysicalProjection.FieldRows
