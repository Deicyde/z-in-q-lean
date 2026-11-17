import Std

namespace ReviewedPole

def Weak (B d : Rat) : Prop :=
  ∃ e s v p q : Rat, (1-e)*(1+3*e)=B*p^2 ∧ s*v=d*e ∧ (s-v)*(s+3*v)=B*q^2

def Compressed (B d : Rat) : Prop :=
  ∃ s v P q : Rat, (d-s*v)*(d+3*s*v)=B*P^2 ∧ (s-v)*(s+3*v)=B*q^2

private theorem cancel {x y m : Rat} (hm : m≠0) (eq : x*m=y*m) : x=y := by grind

/-- The 245-table substitution, including its singular outside value. -/
theorem compression (B : Rat) : Weak B (289-B) ↔ Compressed B (289-B) := by
  let d := 289-B
  change Weak B d ↔ Compressed B d
  constructor
  · rintro ⟨e,s,v,p,q,hp,hv,hq⟩
    refine ⟨s,v,d*p,q,?_,hq⟩
    calc (d-s*v)*(d+3*s*v) = d^2*((1-e)*(1+3*e)) := by rw [hv]; grobner
         _ = B*(d*p)^2 := by rw [hp]; grobner
  · rintro ⟨s,v,P,q,hP,hq⟩
    by_cases hz : d=0
    · have hd : 289-B=0 := hz
      have hB : B=289 := by grind
      rw [hz,hB]
      have unit : (1/17:Rat)*17=1 := Rat.div_mul_cancel (by decide)
      exact ⟨0,0,0,1/17,0,by grobner,by grobner,by grobner⟩
    · let e := s*v/d
      let p := P/d
      have he : e*d=s*v := Rat.div_mul_cancel hz
      have hp : p*d=P := Rat.div_mul_cancel hz
      refine ⟨e,s,v,p,q,?_,by rw [←he]; grobner,hq⟩
      apply cancel (m := d^2) (by grind)
      calc (1-e)*(1+3*e)*d^2 = (d-e*d)*(d+3*(e*d)) := by grobner
           _ = B*P^2 := by rw [he]; grobner
           _ = B*p^2*d^2 := by rw [←hp]; grobner

/-- Clearing the denominators of the explicit simultaneous conic points. -/
private theorem fromIdentities (c T h x y n₁ n₂ : Rat)
    (hc : c≠0) (hT : T≠0) (hh : h≠0) (hy : y≠0)
    (one : (T*h+x^2)*(T*h-3*x^2) = -3*n₁^2)
    (two : (h+y^2)*(h-3*y^2) = -3*n₂^2) :
    Weak (-3*c^2) (289*T) := by
  let e := -x^2/(T*h)
  let s := 17*x/y
  let v := -17*x*y/h
  let p := n₁/(c*(T*h))
  let q := 17*x*n₂/(c*(h*y))
  have he : e*(T*h) = -x^2 := Rat.div_mul_cancel (by grind)
  have hs : s*y = 17*x := Rat.div_mul_cancel hy
  have hv : v*h = -17*x*y := Rat.div_mul_cancel hh
  have hp : p*(c*(T*h)) = n₁ := Rat.div_mul_cancel (by grind)
  have hq : q*(c*(h*y)) = 17*x*n₂ := Rat.div_mul_cancel (by grind)
  refine ⟨e,s,v,p,q,?_,?_,?_⟩
  · apply cancel (m := (T*h)^2) (by grind)
    calc (1-e)*(1+3*e)*(T*h)^2 = (T*h-e*(T*h))*(T*h+3*(e*(T*h))) := by grobner
         _ = (T*h+x^2)*(T*h-3*x^2) := by rw [he]; grobner
         _ = -3*n₁^2 := one
         _ = (-3*c^2*p^2)*(T*h)^2 := by rw [←hp]; grobner
  · apply cancel (m := h*y) (by grind)
    calc (s*v)*(h*y) = (s*y)*(v*h) := by grobner
         _ = 289*y*(-x^2) := by rw [hs,hv]; grobner
         _ = (289*T*e)*(h*y) := by rw [←he]; grobner
  · apply cancel (m := (h*y)^2) (by grind)
    calc (s-v)*(s+3*v)*(h*y)^2 =
             ((s*y)*h-(v*h)*y)*((s*y)*h+3*(v*h)*y) := by grobner
         _ = (17*x)^2*((h+y^2)*(h-3*y^2)) := by rw [hs,hv]; grobner
         _ = -3*(17*x*n₂)^2 := by rw [two]; grobner
         _ = (-3*c^2*q^2)*(h*y)^2 := by rw [←hq]; grobner

/-- Rational physical witnesses on the entire exceptional signed branch. -/
theorem minusThree (c T : Rat) (hc : c≠0) (hT : 0<T) : Weak (-3*c^2) (289*T) := by
  let h := 24*(T+1)*(T+3)*(3*T+1)
  let x := 7*T^2+6*T+3
  let y := 3*T^2+6*T+7
  let n₁ := (T-1)*(5*T+3)*(11*T^2+18*T+3)
  let n₂ := (T-1)*(3*T+5)*(3*T^2+18*T+11)
  apply fromIdentities c T h x y n₁ n₂ hc (by grind)
  · change 24*(T+1)*(T+3)*(3*T+1) ≠ 0
    have pos : 0 < 24*(T+1)*(T+3)*(3*T+1) :=
      Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by decide) (by grind)) (by grind)) (by grind)
    grind
  · change 3*T^2+6*T+7 ≠ 0
    have pos := Rat.mul_pos hT hT
    grind
  · dsimp [h,x,n₁]; grobner
  · dsimp [h,y,n₂]; grobner

theorem signedPhysical (c : Rat) (hc : c≠0) : Weak (-3*c^2) (289-(-3*c^2)) := by
  let T := (289-(-3*c^2))/289
  have hT : T*289 = 289-(-3*c^2) := Rat.div_mul_cancel (by decide)
  have pos : 0<T := by
    have square : 0 ≤ c*c := by
      by_cases h : 0≤c
      · exact Rat.mul_nonneg h h
      · have positive : 0≤ -c := by grind
        have nn := Rat.mul_nonneg positive positive
        grind
    grind
  rw [←hT, Rat.mul_comm T 289]
  exact minusThree c T hc pos

end ReviewedPole

#print axioms ReviewedPole.compression
#print axioms ReviewedPole.minusThree
#print axioms ReviewedPole.signedPhysical
