import SparseField
namespace PhysicalProjection.FieldRows
open ZeroInput.Sparse ProjectionDescent PhysicalProjection.Comparison Sparse
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000
def b0n : Polynomial := [⟨(-348:Int),[6]⟩,⟨(258:Int),[7]⟩,⟨(-320:Int),[176]⟩,⟨(848:Int),[177]⟩,⟨(-164:Int),[6, 6, 176]⟩,⟨(574:Int),[6, 6, 177]⟩,⟨(1148:Int),[6, 7, 176]⟩,⟨(-656:Int),[6, 7, 177]⟩,⟨(-328:Int),[7, 7, 176]⟩,⟨(1148:Int),[7, 7, 177]⟩]
theorem b0value (x : Assignment) : value x b0n = 164*(plainB .S x).1 := by
  simp [b0n,plainB,Block.h,field,times,sq,plus,aa,bb,invAA,D2,value,termValue,monomialValue] <;> grobner
def b1n : Polynomial := [⟨(129:Int),[6]⟩,⟨(-348:Int),[7]⟩,⟨(424:Int),[176]⟩,⟨(-320:Int),[177]⟩,⟨(287:Int),[6, 6, 176]⟩,⟨(-164:Int),[6, 6, 177]⟩,⟨(-328:Int),[6, 7, 176]⟩,⟨(1148:Int),[6, 7, 177]⟩,⟨(574:Int),[7, 7, 176]⟩,⟨(-328:Int),[7, 7, 177]⟩]
theorem b1value (x : Assignment) : value x b1n = 164*(plainB .S x).2 := by
  simp [b1n,plainB,Block.h,field,times,sq,plus,aa,bb,invAA,D2,value,termValue,monomialValue] <;> grobner

abbrev FP := Polynomial × Polynomial
def vars (i : Nat) : FP := (vp i,vp (i+1))
def addF (a b : FP) : FP := (ap a.1 b.1,ap a.2 b.2)
def scaleF (n : Int) (a : FP) : FP := (sp n a.1,sp n a.2)
def mulF (a b : FP) : FP := (ap (mp a.1 b.1) (sp 2 (mp a.2 b.2)),ap (mp a.1 b.2) (mp a.2 b.1))
def FVal (z : Assignment) (a : FP) : Q2 := (value z a.1,value z a.2)
def DA : FP := (cp 11,cp (-6))
def BS : FP := (b0n,b1n)
def CS := mulF (vars 6) (vars 6)
def QS := scaleF (-1) (mulF (vars 54) (vars 70))
def RF := addF (mulF BS BS) (scaleF (164^2) (addF DA (scaleF (-1) (mulF CS CS))))
def SF := addF (mulF BS QS) (scaleF 164 (addF (mulF (vars 6) (vars 54)) (addF (mulF CS (vars 20)) (mulF DA (mulF QS (vars 52))))))
theorem r_sem (x : Assignment) : FVal x RF=scale (164^2) (plain false .S .root x) := by
  apply Prod.ext <;> simp only [FVal,RF,mulF,addF,scaleF,BS,CS,DA,vars,at_c,at_v,at_m,at_a,at_s,b0value,b1value]
  all_goals dsimp only [plain,coreFormula,minus,plus,scale,D2,Block.h,Block.number,field,sq,times] <;> grobner

theorem s_sem (x : Assignment) : FVal x SF=scale 164 (plain false .S .second x) := by
  apply Prod.ext <;> simp only [FVal,SF,mulF,addF,scaleF,BS,CS,QS,DA,vars,at_c,at_v,at_m,at_a,at_s,b0value,b1value]
  all_goals dsimp only [plain,coreFormula,minus,plus,scale,D2,Block.h,Block.number,field,sq,times] <;> grobner
end PhysicalProjection.FieldRows
