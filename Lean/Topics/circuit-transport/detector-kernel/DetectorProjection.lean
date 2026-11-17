import Std

namespace CircuitTransport.Detector

/-- The six source equations, after the existing cube pivot. -/
def Original (e t a q Q : Rat) : Prop :=
  ∃ b c d : Rat, e*(1+a*t^3)=0 ∧ e*b=a^2 ∧ e*a*c=b^2 ∧
    c*d=(e*a)^5 ∧ c*q=d^2 ∧ c*Q=q^4

/-- `D*t` is the numerator of the physical parameter with fixed denominator `D`. -/
def Chart130 (D e t a q Q : Rat) : Prop :=
  ∃ u : Rat, e*(1-e*(D*t)*u)=0 ∧ a= -(D*e*u)^3 ∧
    q=e^19*a ∧ Q=e^79*a+(1-e*(D*t)*u)*u

/-- Outside the six rows, the longer chart exposes the product `e*a`. -/
def Chart133 (e t A q Q : Rat) : Prop :=
  ∃ a : Rat, A=e*a ∧ e*(1+a*t^3)=0 ∧ q=e^19*a ∧ e*(Q-e^79*a)=0

private theorem nonzeroMul {a b : Rat} (ha : a≠0) (hb : b≠0) : a*b≠0 := by
  intro h
  exact (Rat.mul_eq_zero.mp h).elim ha hb

private theorem nonzeroPow {a : Rat} (n : Nat) (ha : a≠0) : a^n≠0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ]; exact nonzeroMul ih ha

private theorem ofPowZero {x : Rat} {n : Nat} (h : x^n=0) : x=0 := by
  by_cases hn : x=0
  · exact hn
  · exact False.elim (nonzeroPow n hn h)

private theorem cancel {r x y : Rat} (hr : r≠0) (h : x*r=y*r) : x=y := by grind

/-- In the singular fibre both consumed intermediate values vanish. The last is free. -/
theorem original_zero (t a q Q : Rat) : Original 0 t a q Q ↔ a=0 ∧ q=0 := by
  constructor
  · rintro ⟨b,c,d,_,ba,_,dc,qc,Qc⟩
    have az : a=0 := ofPowZero (by simpa using ba.symm : a^2=0)
    refine ⟨az,?_⟩
    by_cases hc : c=0
    · exact ofPowZero (by simpa [hc] using Qc.symm : q^4=0)
    · have prodZero : c*d=0 := by simpa using dc
      have dz := (Rat.mul_eq_zero.mp prodZero).resolve_left hc
      have cq : c*q=0 := by simpa [dz] using qc
      exact (Rat.mul_eq_zero.mp cq).resolve_left hc
  · rintro ⟨rfl,rfl⟩
    refine ⟨0,0,0,?_,?_,?_,?_,?_,?_⟩ <;> grobner

/-- The three retained values on the open fibre. -/
theorem original_nonzero {e : Rat} (he : e≠0) (t a q Q : Rat) :
    Original e t a q Q ↔ a*t^3= -1 ∧ q=e^19*a ∧ Q=e^79*a := by
  constructor
  · rintro ⟨b,c,d,lead,eb,eac,cd,cq,cQ⟩
    have hg := (Rat.mul_eq_zero.mp lead).resolve_left he
    have gate : a*t^3= -1 := by grobner
    have ha : a≠0 := by
      intro z
      exact (by decide : (0:Rat)≠ -1) (by simpa [z] using gate)
    have ce : c*e^3 = a^3 := by
      apply cancel ha
      calc c*e^3*a = (e*a*c)*e^2 := by grobner
           _ = (e*b)^2 := by rw [eac]; grobner
           _ = a^3*a := by rw [eb]; grobner
    have hc : c≠0 := by
      intro z
      have az : a^3=0 := by simpa [z] using ce.symm
      exact nonzeroPow 3 ha az
    have dv : d=e^8*a^2 := by
      apply cancel hc
      calc d*c = (e*a)^5 := by rw [Rat.mul_comm d c,cd]
           _ = (a^3)*e^5*a^2 := by grobner
           _ = (e^8*a^2)*c := by rw [←ce]; grobner
    have qv : q=e^19*a := by
      apply cancel hc
      calc q*c = d^2 := by rw [Rat.mul_comm q c,cq]
           _ = (a^3)*e^16*a := by rw [dv]; grobner
           _ = (e^19*a)*c := by rw [←ce]; grobner
    refine ⟨gate,qv,?_⟩
    apply cancel hc
    calc Q*c = q^4 := by rw [Rat.mul_comm Q c,cQ]
         _ = (a^3)*e^76*a := by rw [qv]; grobner
         _ = (e^79*a)*c := by rw [←ce]; grobner
  · rintro ⟨gate,rfl,rfl⟩
    let i := e⁻¹
    have hi : e*i=1 := Rat.mul_inv_cancel e he
    refine ⟨a^2*i,a^3*i^3,e^8*a^2,?_,?_,?_,?_,?_,?_⟩
    · rw [gate]; grobner
    · calc e*(a^2*i) = (e*i)*a^2 := by grobner
           _ = a^2 := by rw [hi]; grobner
    · calc e*a*(a^3*i^3) = (e*i)*a^4*i^2 := by grobner
           _ = (a^2*i)^2 := by rw [hi]; grobner
    · calc a^3*i^3*(e^8*a^2) = (e*i)^3*(e*a)^5 := by grobner
           _ = (e*a)^5 := by rw [hi]; grobner
    · calc a^3*i^3*(e^19*a) = (e*i)^3*(e^8*a^2)^2 := by grobner
           _ = (e^8*a^2)^2 := by rw [hi]; grobner
    · calc a^3*i^3*(e^79*a) = (e*i)^3*(e^19*a)^4 := by grobner
           _ = (e^19*a)^4 := by rw [hi]; grobner

/-- Projection at fixed `e,t,a,q,Q`, for every nonzero fixed denominator. -/
theorem projection130 (D e t a q Q : Rat) (hD : D≠0) :
    Original e t a q Q ↔ Chart130 D e t a q Q := by
  by_cases he : e=0
  · subst e
    rw [original_zero]
    constructor
    · rintro ⟨rfl,rfl⟩
      refine ⟨Q,?_,?_,?_,?_⟩ <;> grobner
    · rintro ⟨u,_,ua,uq,_⟩
      exact ⟨by grobner,by grobner⟩
  · rw [original_nonzero he]
    constructor
    · rintro ⟨gate,qv,Qv⟩
      have ht : t≠0 := by
        intro z
        exact (by decide : (0:Rat)≠ -1) (by simpa [z,Rat.pow_succ] using gate)
      let u := (e*(D*t))⁻¹
      have hu : e*(D*t)*u=1 := Rat.mul_inv_cancel _ (nonzeroMul he (nonzeroMul hD ht))
      have ut : D*e*u*t=1 := by
        calc D*e*u*t = e*(D*t)*u := by grobner
             _ = 1 := hu
      refine ⟨u,?_,?_,qv,?_⟩
      · rw [hu]; grobner
      · apply cancel (nonzeroPow 3 ht)
        calc a*t^3 = -1 := gate
             _ = -(D*e*u*t)^3 := by rw [ut]; decide
             _ = (-(D*e*u)^3)*t^3 := by grobner
      · rw [hu,Qv]; grobner
    · rintro ⟨u,guard,ua,uq,uQ⟩
      have h := (Rat.mul_eq_zero.mp guard).resolve_left he
      have ut : D*e*u*t = 1 := by grobner
      refine ⟨?_,uq,?_⟩
      · calc a*t^3 = -(D*e*u*t)^3 := by rw [ua]; grobner
             _ = -1 := by rw [ut]; decide
      · rw [h] at uQ; grobner

/-- Projection at fixed `e,t,e*a,q,Q` for the variant with a separate final register. -/
theorem projection133 (e t A q Q : Rat) :
    (∃ a : Rat, A=e*a ∧ Original e t a q Q) ↔ Chart133 e t A q Q := by
  by_cases he : e=0
  · subst e
    constructor
    · rintro ⟨a,aa,old⟩
      obtain ⟨az,qz⟩ := (original_zero t a q Q).mp old
      exact ⟨a,aa,by simp,by simp [az,qz],by simp⟩
    · rintro ⟨a,aa,_,qv,_⟩
      refine ⟨0,by simpa using aa,(original_zero t 0 q Q).mpr ⟨rfl,?_⟩⟩
      grobner
  · constructor
    · rintro ⟨a,aa,old⟩
      obtain ⟨gate,qv,Qv⟩ := (original_nonzero he t a q Q).mp old
      exact ⟨a,aa,by rw [gate]; grobner,qv,by rw [Qv]; grobner⟩
    · rintro ⟨a,aa,eg,qv,eQ⟩
      have g := (Rat.mul_eq_zero.mp eg).resolve_left he
      have out := (Rat.mul_eq_zero.mp eQ).resolve_left he
      exact ⟨a,aa,(original_nonzero he t a q Q).mpr ⟨by grobner,qv,by grobner⟩⟩

#print axioms original_zero
#print axioms original_nonzero
#print axioms projection130
#print axioms projection133

end CircuitTransport.Detector
