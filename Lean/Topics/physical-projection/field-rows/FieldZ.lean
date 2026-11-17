import FieldRegistry
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal26 (g : Bool) (z : Assignment) : value z (literal g .Z .root false) = rowScale .Z .root false * component false (formula g .Z .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p26] <;> grobner
theorem literal27 (g : Bool) (z : Assignment) : value z (literal g .Z .root true) = rowScale .Z .root true * component true (formula g .Z .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p27] <;> grobner
theorem literal724 (g : Bool) (z : Assignment) : value z (literal g .Z .first false) = rowScale .Z .first false * component false (formula g .Z .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p724] <;> grobner
theorem literal725 (g : Bool) (z : Assignment) : value z (literal g .Z .first true) = rowScale .Z .first true * component true (formula g .Z .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p725] <;> grobner
theorem literal726 (g : Bool) (z : Assignment) : value z (literal g .Z .second false) = rowScale .Z .second false * component false (formula g .Z .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p726] <;> grobner
theorem literal727 (g : Bool) (z : Assignment) : value z (literal g .Z .second true) = rowScale .Z .second true * component true (formula g .Z .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p727] <;> grobner
theorem literal728 (g : Bool) (z : Assignment) : value z (literal g .Z .product false) = rowScale .Z .product false * component false (formula g .Z .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p728] <;> grobner
theorem literal729 (g : Bool) (z : Assignment) : value z (literal g .Z .product true) = rowScale .Z .product true * component true (formula g .Z .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p729] <;> grobner
theorem literal730 (g : Bool) (z : Assignment) : value z (literal g .Z .quartic false) = rowScale .Z .quartic false * component false (formula g .Z .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p730] <;> grobner
theorem literal731 (g : Bool) (z : Assignment) : value z (literal g .Z .quartic true) = rowScale .Z .quartic true * component true (formula g .Z .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p731] <;> grobner
theorem literal196 (g : Bool) (z : Assignment) : value z (literal g .Z .output false) = rowScale .Z .output false * component false (formula g .Z .output z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p196] <;> grobner
theorem literal197 (g : Bool) (z : Assignment) : value z (literal g .Z .output true) = rowScale .Z .output true * component true (formula g .Z .output z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p197] <;> grobner
theorem literal213 (g : Bool) (z : Assignment) : value z (literal g .Z .iSquare false) = rowScale .Z .iSquare false * component false (formula g .Z .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p213] <;> grobner
theorem literal214 (g : Bool) (z : Assignment) : value z (literal g .Z .iSquare true) = rowScale .Z .iSquare true * component true (formula g .Z .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p214] <;> grobner
theorem literal172 (g : Bool) (z : Assignment) : value z (literal g .Z .kSquare false) = rowScale .Z .kSquare false * component false (formula g .Z .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p172] <;> grobner
theorem literal173 (g : Bool) (z : Assignment) : value z (literal g .Z .kSquare true) = rowScale .Z .kSquare true * component true (formula g .Z .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p173] <;> grobner
end PhysicalProjection.FieldRows
