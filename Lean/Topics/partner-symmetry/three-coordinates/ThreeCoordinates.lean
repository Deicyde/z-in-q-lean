import PoleModels

namespace ThreeCoordinates

def Sextic (B d : Rat) : Prop :=
  ∃ T S W : Rat, W^2*(T^2-B)*(T^2+3*B)=d*(B-S^2)*(B+3*S^2)

private def AtPoint (B d e s v p q : Rat) : Prop :=
  (1-e)*(1+3*e)=B*p^2 ∧ s*v=d*e ∧ (s-v)*(s+3*v)=B*q^2

private theorem cancel {x y m : Rat} (hm : m≠0) (eq : x*m=y*m) : x=y := by grind

/-- The open pair of complementary affine charts, expressed directly in physical coordinates. -/
private theorem toChart {B d e s v p q : Rat} (hB : ¬∃ a : Rat, B=a^2)
    (point : AtPoint B d e s v p q) (h₁ : 1-e≠0) (h₂ : s+3*v≠0) : Sextic B d := by
  obtain ⟨first,link,second⟩ := point
  let T := B*p/(1-e)
  let S := B*q/(s+3*v)
  have a : T*(1-e)=B*p := Rat.div_mul_cancel h₁
  have b : S*(s+3*v)=B*q := Rat.div_mul_cancel h₂
  have ta : T^2*(1-e)=B*(1+3*e) := by
    apply cancel h₁
    calc T^2*(1-e)*(1-e) = (T*(1-e))^2 := by grobner
         _ = B*(B*p^2) := by rw [a]; grobner
         _ = B*(1+3*e)*(1-e) := by rw [←first]; grobner
  have sb : S^2*(s+3*v)=B*(s-v) := by
    apply cancel h₂
    calc S^2*(s+3*v)*(s+3*v) = (S*(s+3*v))^2 := by grobner
         _ = B*(B*q^2) := by rw [b]; grobner
         _ = B*(s-v)*(s+3*v) := by rw [←second]; grobner
  let x := T^2-B
  let y := T^2+3*B
  let m := B-S^2
  let n := B+3*S^2
  have ey : e*y=x := by dsimp [x,y]; grobner
  have sm : s*m=v*n := by dsimp [m,n]; grobner
  have hx : x≠0 := fun h => hB ⟨T,by change T^2-B=0 at h; grobner⟩
  let W := s*m/x
  have wx : W*x=s*m := Rat.div_mul_cancel hx
  refine ⟨T,S,W,?_⟩
  change W^2*x*y=d*m*n
  apply cancel hx
  calc W^2*x*y*x = (W*x)^2*y := by grobner
       _ = (s*m)*(s*m)*y := by rw [wx]; grobner
       _ = (s*m)*(v*n)*y := congrArg (fun k : Rat => (s*m)*k*y) sm
       _ = m*n*(s*v)*y := by grobner
       _ = d*m*n*x := by rw [link,←ey]; grobner

/-- Recover the physical solution without dividing by the new ordinate. -/
private theorem fromChart {B d : Rat} (hB : ¬∃ a : Rat, B=a^2)
    (h₃ : ¬∃ a : Rat, B= -3*a^2) (chart : Sextic B d) : ReviewedPole.Weak B d := by
  obtain ⟨T,S,W,equation⟩ := chart
  let x := T^2-B
  let y := T^2+3*B
  let m := B-S^2
  let n := B+3*S^2
  change W^2*x*y=d*m*n at equation
  have hy : y≠0 := by
    intro h; apply h₃
    have triple : T/3*3=T := Rat.div_mul_cancel (by decide)
    exact ⟨T/3,by change T^2+3*B=0 at h; grobner⟩
  have hm : m≠0 := fun h => hB ⟨S,by change B-S^2=0 at h; grobner⟩
  have hn : n≠0 := fun h => h₃ ⟨S,by change B+3*S^2=0 at h; grobner⟩
  let e := x/y
  let p := 4*T/y
  let s := W*x/m
  let v := W*x/n
  let q := 4*S*v/m
  have ey : e*y=x := Rat.div_mul_cancel hy
  have py : p*y=4*T := Rat.div_mul_cancel hy
  have sm : s*m=W*x := Rat.div_mul_cancel hm
  have vn : v*n=W*x := Rat.div_mul_cancel hn
  have qm : q*m=4*S*v := Rat.div_mul_cancel hm
  refine ⟨e,s,v,p,q,?_,?_,?_⟩
  · apply cancel (m := y^2) (by grind)
    calc (1-e)*(1+3*e)*y^2 = (y-e*y)*(y+3*(e*y)) := by grobner
         _ = (y-x)*(y+3*x) := by rw [ey]
         _ = B*(4*T)^2 := by dsimp [x,y]; grobner
         _ = B*p^2*y^2 := by rw [←py]; grobner
  · apply cancel (m := m*n*y) (by grind)
    calc s*v*(m*n*y) = (s*m)*(v*n)*y := by grobner
         _ = x*(W^2*x*y) := by rw [sm,vn]; grobner
         _ = (d*e)*(m*n*y) := by rw [equation,←ey]; grobner
  · apply cancel (m := m^2) (by grind)
    calc (s-v)*(s+3*v)*m^2 = (s*m-v*m)*(s*m+3*(v*m)) := by grobner
         _ = v^2*((n-m)*(n+3*m)) := by rw [sm,←vn]; grobner
         _ = B*(4*S*v)^2 := by dsimp [m,n]; grobner
         _ = B*q^2*m^2 := by rw [←qm]; grobner

/-- If the original ordering misses a chart, interchange the conics.
    Repeated excluded endpoints are dealt with separately by d=s². -/
private theorem alternate {B d e s v p q : Rat} (hB : ¬∃ a : Rat, B=a^2)
    (point : AtPoint B d e s v p q) (hs : s≠0) (hd : d≠0) (distinct : d≠s^2)
    (miss : 1-e=0 ∨ s+3*v=0) : Sextic B d := by
  obtain ⟨first,link,second⟩ := point
  let E := v/s
  let S := d/s
  let P := q/s
  let Q := d*p/s
  have he : E*s=v := Rat.div_mul_cancel hs
  have hₛ : S*s=d := Rat.div_mul_cancel hs
  have hp : P*s=q := Rat.div_mul_cancel hs
  have hq : Q*s=d*p := Rat.div_mul_cancel hs
  apply toChart (e := E) (s := S) (v := v) (p := P) (q := Q) hB
  · refine ⟨?_,?_,?_⟩
    · apply cancel (m := s^2) (by grind)
      calc (1-E)*(1+3*E)*s^2 = (s-E*s)*(s+3*(E*s)) := by grobner
           _ = B*q^2 := by rw [he]; exact second
           _ = B*P^2*s^2 := by rw [←hp]; grobner
    · apply cancel hs
      calc S*v*s = (S*s)*v := by grobner
           _ = (d*E)*s := by rw [hₛ,←he]; grobner
    · apply cancel (m := s^2) (by grind)
      calc (S-v)*(S+3*v)*s^2 = (S*s-s*v)*(S*s+3*(s*v)) := by grobner
           _ = d^2*((1-e)*(1+3*e)) := by rw [hₛ,link]; grobner
           _ = B*(d*p)^2 := by rw [first]; grobner
           _ = B*Q^2*s^2 := by rw [←hq]; grobner
  · intro equal
    have same : v=s := by grobner
    rcases miss with m|m
    · apply distinct; rw [same] at link; grobner
    · apply hs; grobner
  · intro equal
    have collapse : d+3*(s*v)=0 := by grobner
    rcases miss with m|m
    · apply hd; grobner
    · apply distinct; grobner

private theorem forward {B : Rat} (hB : ¬∃ a : Rat, B=a^2)
    (point : ReviewedPole.Weak B (289-B)) : Sextic B (289-B) := by
  let d := 289-B
  obtain ⟨e,s,v,p,q,first,link,second⟩ := point
  change s*v=d*e at link
  have old : AtPoint B d e s v p q := ⟨first,link,second⟩
  by_cases same : d=s^2
  · refine ⟨1,B,B*s,?_⟩
    change (B*s)^2*(1^2-B)*(1^2+3*B)=d*(B-B^2)*(B+3*B^2)
    rw [same]; grobner
  have hd : d≠0 := fun h => hB ⟨17,by change 289-B=0 at h; grobner⟩
  have he : e≠0 := by
    intro h; rw [h] at first
    have unit : B*p^2=1 := by grobner
    exact hB ⟨B*p,by grobner⟩
  have hs : s≠0 := by intro zero; rw [zero] at link; grind
  by_cases one : 1-e=0
  · exact alternate hB old hs hd same (Or.inl one)
  by_cases two : s+3*v=0
  · exact alternate hB old hs hd same (Or.inr two)
  exact toChart hB old one two

/-- Every B, including zero, the two rational squareclasses, and the singular value 289. -/
theorem weak_iff_sextic (B : Rat) :
    ReviewedPole.Weak B (289-B) ↔
      ∃ T S W : Rat, W^2*(T^2-B)*(T^2+3*B)=(289-B)*(B-S^2)*(B+3*S^2) := by
  change ReviewedPole.Weak B (289-B) ↔ Sextic B (289-B)
  by_cases sq : ∃ a : Rat, B=a^2
  · obtain ⟨a,ha⟩ := sq
    constructor
    · intro _; exact ⟨0,a,0,by rw [ha]; grobner⟩
    · intro _
      by_cases ha0 : a=0
      · have zero : B=0 := by grobner
        rw [zero]; exact ⟨1,17,17,0,0,by grobner,by grobner,by grobner⟩
      · let p := 1/a
        have hp : p*a=1 := Rat.div_mul_cancel ha0
        refine ⟨0,0,0,p,0,?_,by grobner,by grobner⟩
        calc (1-0)*(1+3*0) = (p*a)^2 := by rw [hp]; grobner
             _ = B*p^2 := by rw [ha]; grobner
  by_cases negative : ∃ a : Rat, B= -3*a^2
  · obtain ⟨a,ha⟩ := negative
    have nz : a≠0 := fun zero => sq ⟨0,by grobner⟩
    rw [ha]
    exact ⟨fun _ => ⟨0,a,0,by grobner⟩,fun _ => ReviewedPole.signedPhysical a nz⟩
  exact ⟨forward sq,fromChart sq negative⟩

end ThreeCoordinates

#print axioms ThreeCoordinates.weak_iff_sextic
