import PDPoleSupport1
import ThreeCoordinates
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

set_option linter.unusedSimpArgs false
private theorem raw (x : Assignment) (e s v p q : Rat) (he : x 35=(17:Rat)*e) (hs : x 36=(1:Rat)*s) (hv : x 157=((1:Rat)/17)*v) (hp : x 37=(17:Rat)*p) (hq : x 38=(1:Rat)*q) :
    (value x p339=0 ∧ value x p341=0 ∧ value x p344=0) ↔ ((1-e)*(1+3*e)=((17:Rat)*x 156)*p^2 ∧ s*v=(289-((17:Rat)*x 156))*e ∧ (s-v)*(s+3*v)=((17:Rat)*x 156)*q^2) := by
  have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
  have first : value x p339=(289:Rat)*((1-e)*(1+3*e)-((17:Rat)*x 156)*p^2) := by
    simp only [p339,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have middle : value x p341=(-1:Rat)*(s*v-(289-((17:Rat)*x 156))*e) := by
    simp only [p341,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have last : value x p344=(1:Rat)*((s-v)*(s+3*v)-((17:Rat)*x 156)*q^2) := by
    simp only [p344,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  rw [first,middle,last]
  constructor <;> rintro ⟨ha,hm,hz⟩ <;> exact ⟨by grobner,by grobner,by grobner⟩
private theorem newRow (x : Assignment) : value x sextic1=0 ↔ (x 38)^2*((x 36)^2-((17:Rat)*x 156))*((x 36)^2+3*((17:Rat)*x 156))=(289-((17:Rat)*x 156))*(((17:Rat)*x 156)-(x 37)^2)*(((17:Rat)*x 156)+3*(x 37)^2) := by
  simp only [sextic1,value_append,value,termValue,monomialValue]; constructor <;> intro h <;> grobner
private theorem toNew (x : Assignment) (first : value x p339=0) (middle : value x p341=0) (last : value x p344=0) :
    ∃ y, off [35,36,157,37,38] x y ∧ value y sextic1=0 := by
    have recover (u c : Rat) (hn : c≠0) : u=c*(u/c) := by have h := Rat.div_mul_cancel (a:=u) hn; grobner
    have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
    have old : ReviewedPole.Weak ((17:Rat)*x 156) (289-((17:Rat)*x 156)) := by
      refine ⟨x 35/(17:Rat),x 36/(1:Rat),x 157/((1:Rat)/17),x 37/(17:Rat),x 38/(1:Rat),?_⟩
      apply (raw x _ _ _ _ _ (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind))).mp
      exact ⟨first,middle,last⟩
    obtain ⟨T,S,W,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 156)).mp old
    let patch : List (Nat×Rat) := [(35,0),(36,T),(157,0),(37,S),(38,W)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,(newRow y).mpr ?_⟩
    exact spec
private theorem toOld (x : Assignment) (row : value x sextic1=0) :
    ∃ y, off [35,36,157,37,38] x y ∧ value y p339=0 ∧ value y p341=0 ∧ value y p344=0 := by
    obtain ⟨e,s,v,p,q,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 156)).mpr ⟨x 36,x 37,x 38,(newRow x).mp row⟩
    let patch : List (Nat×Rat) := [(35,(17:Rat)*e),(36,(1:Rat)*s),(157,((1:Rat)/17)*v),(37,(17:Rat)*p),(38,(1:Rat)*q)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,?_⟩
    exact (raw y e s v p q rfl rfl rfl rfl rfl).mpr spec
theorem physical1 (g : Bool) (X : Rat) : project parentIds (original g) X ↔ project poleI1 (poleF1 g) X :=
  pole_project parentIds (original g) 339 341 344 sextic1 [35,36,157,37,38] (by decide) (by decide) (by decide) (by decide)
    (outside1 g) toNew toOld X
end ProjectionDescent.Shared
