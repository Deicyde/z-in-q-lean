import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal713 (g : Bool) (z : Assignment) : value z (literal g .S .product true) = rowScale .S .product true * component true (formula g .S .product z) := by
  have small (v : Assignment) : value v small713=3*(rowScale .S .product true * component true (plain g .S .product v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small713] <;> grobner
  have e:=congrArg (value z) data713
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p713=rowScale .S .product true * component true (plain g .S .product (shifted z))
  grobner
end PhysicalProjection.FieldRows
