import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal189 (g : Bool) (z : Assignment) : value z (literal g .S .output true) = rowScale .S .output true * component true (formula g .S .output z) := by
  have small (v : Assignment) : value v small189=3*(rowScale .S .output true * component true (plain g .S .output v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small189] <;> grobner
  have e:=congrArg (value z) data189
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p189=rowScale .S .output true * component true (plain g .S .output (shifted z))
  grobner
end PhysicalProjection.FieldRows
