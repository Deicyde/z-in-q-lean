import PDPoleSupport3
import ThreeCoordinates
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

set_option linter.unusedSimpArgs false
private theorem raw (x : Assignment) (e s v p q : Rat) (he : x 43=(17:Rat)*e) (hs : x 44=(1:Rat)*s) (hv : x 188=((1:Rat)/17)*v) (hp : x 45=(17:Rat)*p) (hq : x 46=(1:Rat)*q) :
    (value x p439=0 ∧ value x p441=0 ∧ value x p444=0) ↔ ((1-e)*(1+3*e)=((17:Rat)*x 187)*p^2 ∧ s*v=(289-((17:Rat)*x 187))*e ∧ (s-v)*(s+3*v)=((17:Rat)*x 187)*q^2) := by
  have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
  have first : value x p439=(289:Rat)*((1-e)*(1+3*e)-((17:Rat)*x 187)*p^2) := by
    simp only [p439,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have middle : value x p441=(-1:Rat)*(s*v-(289-((17:Rat)*x 187))*e) := by
    simp only [p441,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have last : value x p444=(1:Rat)*((s-v)*(s+3*v)-((17:Rat)*x 187)*q^2) := by
    simp only [p444,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  rw [first,middle,last]
  constructor <;> rintro ⟨ha,hm,hz⟩ <;> exact ⟨by grobner,by grobner,by grobner⟩
private theorem newRow (x : Assignment) : value x sextic3=0 ↔ (x 46)^2*((x 44)^2-((17:Rat)*x 187))*((x 44)^2+3*((17:Rat)*x 187))=(289-((17:Rat)*x 187))*(((17:Rat)*x 187)-(x 45)^2)*(((17:Rat)*x 187)+3*(x 45)^2) := by
  simp only [sextic3,value_append,value,termValue,monomialValue]; constructor <;> intro h <;> grobner
private theorem toNew (x : Assignment) (first : value x p439=0) (middle : value x p441=0) (last : value x p444=0) :
    ∃ y, off [43,44,188,45,46] x y ∧ value y sextic3=0 := by
    have recover (u c : Rat) (hn : c≠0) : u=c*(u/c) := by have h := Rat.div_mul_cancel (a:=u) hn; grobner
    have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
    have old : ReviewedPole.Weak ((17:Rat)*x 187) (289-((17:Rat)*x 187)) := by
      refine ⟨x 43/(17:Rat),x 44/(1:Rat),x 188/((1:Rat)/17),x 45/(17:Rat),x 46/(1:Rat),?_⟩
      apply (raw x _ _ _ _ _ (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind))).mp
      exact ⟨first,middle,last⟩
    obtain ⟨T,S,W,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 187)).mp old
    let patch : List (Nat×Rat) := [(43,0),(44,T),(188,0),(45,S),(46,W)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,(newRow y).mpr ?_⟩
    exact spec
private theorem toOld (x : Assignment) (row : value x sextic3=0) :
    ∃ y, off [43,44,188,45,46] x y ∧ value y p439=0 ∧ value y p441=0 ∧ value y p444=0 := by
    obtain ⟨e,s,v,p,q,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 187)).mpr ⟨x 44,x 45,x 46,(newRow x).mp row⟩
    let patch : List (Nat×Rat) := [(43,(17:Rat)*e),(44,(1:Rat)*s),(188,((1:Rat)/17)*v),(45,(17:Rat)*p),(46,(1:Rat)*q)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,?_⟩
    exact (raw y e s v p q rfl rfl rfl rfl rfl).mpr spec
theorem physical3 (g : Bool) (X : Rat) : project poleI2 (poleF2 g) X ↔ project poleI3 (poleF3 g) X :=
  pole_project poleI2 (poleF2 g) 439 441 444 sextic3 [43,44,188,45,46] (by decide) (by decide) (by decide) (by decide)
    (outside3 g) toNew toOld X
end ProjectionDescent.Shared
