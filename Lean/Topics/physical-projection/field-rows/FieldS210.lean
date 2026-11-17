import FieldNormal
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal210 (g : Bool) (z : Assignment) : value z (literal g .S .iSquare true) = rowScale .S .iSquare true * component true (formula g .S .iSquare z) := by
  have small (v : Assignment) : value v small210=3*(rowScale .S .iSquare true * component true (plain g .S .iSquare v)) := by
    simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,small210] <;> grobner
  have e:=congrArg (value z) data210
  rw [ProjectionDescent.scale_value,inflate_value,small] at e
  change value z p210=rowScale .S .iSquare true * component true (plain g .S .iSquare (shifted z))
  grobner
end PhysicalProjection.FieldRows
