import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal714 (g : Bool) (z : Assignment) : value z (literal g .S .quartic false) = rowScale .S .quartic false * component false (formula g .S .quartic z) := by
  have small (v : Assignment) : value v small714=3*(rowScale .S .quartic false * component false (plain g .S .quartic v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small714] <;> grobner
  have e:=congrArg (value z) data714
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p714=rowScale .S .quartic false * component false (plain g .S .quartic (shifted z))
  grobner
end PhysicalProjection.FieldRows
