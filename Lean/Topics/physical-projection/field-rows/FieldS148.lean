import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal148 (g : Bool) (z : Assignment) : value z (literal g .S .kSquare false) = rowScale .S .kSquare false * component false (formula g .S .kSquare z) := by
  have small (v : Assignment) : value v small148=3*(rowScale .S .kSquare false * component false (plain g .S .kSquare v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small148] <;> grobner
  have e:=congrArg (value z) data148
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p148=rowScale .S .kSquare false * component false (plain g .S .kSquare (shifted z))
  grobner
end PhysicalProjection.FieldRows
