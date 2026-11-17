import PDPoleSupport2
import ThreeCoordinates
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

set_option linter.unusedSimpArgs false
private theorem raw (x : Assignment) (e s v p q : Rat) (he : x 39=(17:Rat)*e) (hs : x 40=(1:Rat)*s) (hv : x 172=((1:Rat)/17)*v) (hp : x 41=(17:Rat)*p) (hq : x 42=(1:Rat)*q) :
    (value x p389=0 ∧ value x p391=0 ∧ value x p394=0) ↔ ((1-e)*(1+3*e)=((17:Rat)*x 171)*p^2 ∧ s*v=(289-((17:Rat)*x 171))*e ∧ (s-v)*(s+3*v)=((17:Rat)*x 171)*q^2) := by
  have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
  have first : value x p389=(289:Rat)*((1-e)*(1+3*e)-((17:Rat)*x 171)*p^2) := by
    simp only [p389,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have middle : value x p391=(-1:Rat)*(s*v-(289-((17:Rat)*x 171))*e) := by
    simp only [p391,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  have last : value x p394=(1:Rat)*((s-v)*(s+3*v)-((17:Rat)*x 171)*q^2) := by
    simp only [p394,value_append,value,termValue,monomialValue,he,hs,hv,hp,hq]; grobner
  rw [first,middle,last]
  constructor <;> rintro ⟨ha,hm,hz⟩ <;> exact ⟨by grobner,by grobner,by grobner⟩
private theorem newRow (x : Assignment) : value x sextic2=0 ↔ (x 42)^2*((x 40)^2-((17:Rat)*x 171))*((x 40)^2+3*((17:Rat)*x 171))=(289-((17:Rat)*x 171))*(((17:Rat)*x 171)-(x 41)^2)*(((17:Rat)*x 171)+3*(x 41)^2) := by
  simp only [sextic2,value_append,value,termValue,monomialValue]; constructor <;> intro h <;> grobner
private theorem toNew (x : Assignment) (first : value x p389=0) (middle : value x p391=0) (last : value x p394=0) :
    ∃ y, off [39,40,172,41,42] x y ∧ value y sextic2=0 := by
    have recover (u c : Rat) (hn : c≠0) : u=c*(u/c) := by have h := Rat.div_mul_cancel (a:=u) hn; grobner
    have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
    have old : ReviewedPole.Weak ((17:Rat)*x 171) (289-((17:Rat)*x 171)) := by
      refine ⟨x 39/(17:Rat),x 40/(1:Rat),x 172/((1:Rat)/17),x 41/(17:Rat),x 42/(1:Rat),?_⟩
      apply (raw x _ _ _ _ _ (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind)) (recover _ _ (by grind))).mp
      exact ⟨first,middle,last⟩
    obtain ⟨T,S,W,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 171)).mp old
    let patch : List (Nat×Rat) := [(39,0),(40,T),(172,0),(41,S),(42,W)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,(newRow y).mpr ?_⟩
    exact spec
private theorem toOld (x : Assignment) (row : value x sextic2=0) :
    ∃ y, off [39,40,172,41,42] x y ∧ value y p389=0 ∧ value y p391=0 ∧ value y p394=0 := by
    obtain ⟨e,s,v,p,q,spec⟩ := (ThreeCoordinates.weak_iff_sextic ((17:Rat)*x 171)).mpr ⟨x 40,x 41,x 42,(newRow x).mp row⟩
    let patch : List (Nat×Rat) := [(39,(17:Rat)*e),(40,(1:Rat)*s),(172,((1:Rat)/17)*v),(41,(17:Rat)*p),(42,(1:Rat)*q)]
    let y := overlay x patch
    refine ⟨y,overlay_off x patch,?_⟩
    exact (raw y e s v p q rfl rfl rfl rfl rfl).mpr spec
theorem physical2 (g : Bool) (X : Rat) : project poleI1 (poleF1 g) X ↔ project poleI2 (poleF2 g) X :=
  pole_project poleI1 (poleF1 g) 389 391 394 sextic2 [39,40,172,41,42] (by decide) (by decide) (by decide) (by decide)
    (outside2 g) toNew toOld X
end ProjectionDescent.Shared
