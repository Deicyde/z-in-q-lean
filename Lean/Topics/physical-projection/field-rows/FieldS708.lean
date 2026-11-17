import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal708 (g : Bool) (z : Assignment) : value z (literal g .S .first false) = rowScale .S .first false * component false (formula g .S .first z) := by
  have small (v : Assignment) : value v small708=3*(rowScale .S .first false * component false (plain g .S .first v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small708] <;> grobner
  have e:=congrArg (value z) data708
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p708=rowScale .S .first false * component false (plain g .S .first (shifted z))
  grobner
end PhysicalProjection.FieldRows
