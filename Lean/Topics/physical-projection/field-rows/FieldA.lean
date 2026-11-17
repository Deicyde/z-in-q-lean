import FieldRegistry
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal2 (g : Bool) (z : Assignment) : value z (literal g .A .root false) = rowScale .A .root false * component false (formula g .A .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p2] <;> grobner
theorem literal3 (g : Bool) (z : Assignment) : value z (literal g .A .root true) = rowScale .A .root true * component true (formula g .A .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p3] <;> grobner
theorem literal700 (g : Bool) (z : Assignment) : value z (literal g .A .first false) = rowScale .A .first false * component false (formula g .A .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p700] <;> grobner
theorem literal701 (g : Bool) (z : Assignment) : value z (literal g .A .first true) = rowScale .A .first true * component true (formula g .A .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p701] <;> grobner
theorem literal702 (g : Bool) (z : Assignment) : value z (literal g .A .second false) = rowScale .A .second false * component false (formula g .A .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p702] <;> grobner
theorem literal703 (g : Bool) (z : Assignment) : value z (literal g .A .second true) = rowScale .A .second true * component true (formula g .A .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p703] <;> grobner
theorem literal704 (g : Bool) (z : Assignment) : value z (literal g .A .product false) = rowScale .A .product false * component false (formula g .A .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p704] <;> grobner
theorem literal705 (g : Bool) (z : Assignment) : value z (literal g .A .product true) = rowScale .A .product true * component true (formula g .A .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p705] <;> grobner
theorem literal706 (g : Bool) (z : Assignment) : value z (literal g .A .quartic false) = rowScale .A .quartic false * component false (formula g .A .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p706] <;> grobner
theorem literal707 (g : Bool) (z : Assignment) : value z (literal g .A .quartic true) = rowScale .A .quartic true * component true (formula g .A .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p707] <;> grobner
theorem literal184 (g : Bool) (z : Assignment) : value z (literal g .A .output false) = rowScale .A .output false * component false (formula g .A .output z) := by
  cases g <;> simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p184a,p184b] <;> grobner
theorem literal185 (g : Bool) (z : Assignment) : value z (literal g .A .output true) = rowScale .A .output true * component true (formula g .A .output z) := by
  cases g <;> simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p185a,p185b] <;> grobner
theorem literal207 (g : Bool) (z : Assignment) : value z (literal g .A .iSquare false) = rowScale .A .iSquare false * component false (formula g .A .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p207] <;> grobner
theorem literal208 (g : Bool) (z : Assignment) : value z (literal g .A .iSquare true) = rowScale .A .iSquare true * component true (formula g .A .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p208] <;> grobner
theorem literal142 (g : Bool) (z : Assignment) : value z (literal g .A .kSquare false) = rowScale .A .kSquare false * component false (formula g .A .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p142] <;> grobner
theorem literal143 (g : Bool) (z : Assignment) : value z (literal g .A .kSquare true) = rowScale .A .kSquare true * component true (formula g .A .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p143] <;> grobner
end PhysicalProjection.FieldRows
