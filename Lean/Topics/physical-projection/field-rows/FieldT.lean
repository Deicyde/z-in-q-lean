import FieldRegistry
namespace PhysicalProjection.FieldRows
open PhysicalProjection.Comparison ZeroInput.Sparse ProjectionDescent Triangular.Data
set_option linter.unusedSimpArgs false
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
theorem literal18 (g : Bool) (z : Assignment) : value z (literal g .T .root false) = rowScale .T .root false * component false (formula g .T .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p18] <;> grobner
theorem literal19 (g : Bool) (z : Assignment) : value z (literal g .T .root true) = rowScale .T .root true * component true (formula g .T .root z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p19] <;> grobner
theorem literal716 (g : Bool) (z : Assignment) : value z (literal g .T .first false) = rowScale .T .first false * component false (formula g .T .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p716] <;> grobner
theorem literal717 (g : Bool) (z : Assignment) : value z (literal g .T .first true) = rowScale .T .first true * component true (formula g .T .first z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p717] <;> grobner
theorem literal718 (g : Bool) (z : Assignment) : value z (literal g .T .second false) = rowScale .T .second false * component false (formula g .T .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p718] <;> grobner
theorem literal719 (g : Bool) (z : Assignment) : value z (literal g .T .second true) = rowScale .T .second true * component true (formula g .T .second z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p719] <;> grobner
theorem literal720 (g : Bool) (z : Assignment) : value z (literal g .T .product false) = rowScale .T .product false * component false (formula g .T .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p720] <;> grobner
theorem literal721 (g : Bool) (z : Assignment) : value z (literal g .T .product true) = rowScale .T .product true * component true (formula g .T .product z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p721] <;> grobner
theorem literal722 (g : Bool) (z : Assignment) : value z (literal g .T .quartic false) = rowScale .T .quartic false * component false (formula g .T .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p722] <;> grobner
theorem literal723 (g : Bool) (z : Assignment) : value z (literal g .T .quartic true) = rowScale .T .quartic true * component true (formula g .T .quartic z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p723] <;> grobner
theorem literal192 (g : Bool) (z : Assignment) : value z (literal g .T .output false) = rowScale .T .output false * component false (formula g .T .output z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p192] <;> grobner
theorem literal193 (g : Bool) (z : Assignment) : value z (literal g .T .output true) = rowScale .T .output true * component true (formula g .T .output z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p193] <;> grobner
theorem literal211 (g : Bool) (z : Assignment) : value z (literal g .T .iSquare false) = rowScale .T .iSquare false * component false (formula g .T .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p211] <;> grobner
theorem literal212 (g : Bool) (z : Assignment) : value z (literal g .T .iSquare true) = rowScale .T .iSquare true * component true (formula g .T .iSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p212] <;> grobner
theorem literal160 (g : Bool) (z : Assignment) : value z (literal g .T .kSquare false) = rowScale .T .kSquare false * component false (formula g .T .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p160] <;> grobner
theorem literal161 (g : Bool) (z : Assignment) : value z (literal g .T .kSquare true) = rowScale .T .kSquare true * component true (formula g .T .kSquare z) := by
  simp [literal,rowScale,component,formula,plain,plainB,coreFormula,Block.number,Block.h,Block.squareSlot,aval,bval,L,field,scale,plus,minus,aa,bb,invAA,one,D2,sq,times,value,termValue,monomialValue,p161] <;> grobner
end PhysicalProjection.FieldRows
