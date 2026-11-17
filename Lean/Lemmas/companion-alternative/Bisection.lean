import Std

namespace WeakBisection
open Lean.Grind

/-- Recovering the two coordinates of the quadratic norm is reversible. -/
theorem norm_fibre_iff (b t e g k : Rat)
    (ht : 1 - b*t^2 ≠ 0) (hk : (e^2-b*g^2)*k ≠ 0) :
    (∃ z : Rat, z^2 = (1-b*t^2)*((e^2-b*g^2)*k)) ↔
    ∃ h n : Rat, h^2-b*n^2=k ∧ t*(h*e+b*n*g)=h*g+n*e := by
  constructor
  · rintro ⟨z,hz⟩
    have hz0 : z ≠ 0 := by
      intro hzero
      have hp : (1-b*t^2)*((e^2-b*g^2)*k)=0 := by rw [← hz,hzero]; decide
      grind
    have hi : z*z⁻¹=1 := by grind
    refine ⟨k*(e-b*t*g)*z⁻¹,k*(t*e-g)*z⁻¹,?_,?_⟩
    · have hnorm : (e-b*t*g)^2-b*(t*e-g)^2 =
          (1-b*t^2)*(e^2-b*g^2) := by grobner
      calc
        _ = k^2*(z⁻¹)^2*((e-b*t*g)^2-b*(t*e-g)^2) := by grobner
        _ = k*(z⁻¹)^2*((1-b*t^2)*((e^2-b*g^2)*k)) := by rw [hnorm]; grobner
        _ = k := by rw [← hz]; grobner
    · grobner
  · rintro ⟨h,n,hn,he⟩
    let u := h*e+b*n*g
    let v := h*g+n*e
    have hN : u^2-b*v^2=(e^2-b*g^2)*k := by
      dsimp [u,v]
      rw [← hn]
      grobner
    have hv : v=t*u := he.symm
    refine ⟨(1-b*t^2)*u,?_⟩
    rw [← hN,hv]
    grobner

/-- Reconstruct a fractional linear map from a projective slope (B:A). -/
theorem inverse_slope {R : Type} [CommRing R] (b x B A : R) :
    let a := x*B+3*b*A
    let m := x*A-B
    a*x-3*b*m=(x^2+3*b)*B ∧ m*x+a=(x^2+3*b)*A ∧
      a^2+3*b*m^2=(x^2+3*b)*(B^2+3*b*A^2) := by
  dsimp
  refine ⟨?_,?_,?_⟩ <;> grobner

/-- Numerator identities for both directions of stereographic projection. -/
theorem quadric_parameters {R : Type} [CommRing R] (b v w h n a m : R)
    (hq : h^2-b*n^2=a^2+3*b*m^2) :
    (1+b*(v^2+3*w^2))^2-b*(2*v)^2 =
      (1-b*(v^2+3*w^2))^2+3*b*(2*w)^2 ∧
    (h+a)^2+b*(n^2+3*m^2)=2*h*(h+a) ∧
    (h+a)^2-b*(n^2+3*m^2)=2*a*(h+a) := by
  refine ⟨?_,?_,?_⟩ <;> grobner

/-- The degree-two map supplies the weak square after specializing t. -/
theorem bisection_witness {R : Type} [CommRing R] (b t x a m h n : R)
    (hq : h^2-b*n^2=a^2+3*b*m^2) :
    let B := a*x-3*b*m
    let A := m*x+a
    let e := x*B+b*A
    let g := B+x*A
    let u := h*e+b*n*g
    let v := h*g+n*e
    t*u=v →
      ((x^2+3*b)*(1-b*t^2)*u)^2 =
        (1-b*t^2)*(x^2-b)*(x^2+3*b)*(B^2-b*A^2)*(B^2+3*b*A^2) := by
  intro B A e g u v ht
  have hi : B^2+3*b*A^2=(a^2+3*b*m^2)*(x^2+3*b) := by dsimp [A,B]; grobner
  have hj : e^2-b*g^2=(x^2-b)*(B^2-b*A^2) := by dsimp [e,g]; grobner
  have hn : u^2-b*v^2=(h^2-b*n^2)*(e^2-b*g^2) := by dsimp [u,v]; grobner
  rw [hq,hj,← ht] at hn
  rw [hi]
  calc
    _ = (1-b*t^2)*(x^2+3*b)^2*(u^2-b*(t*u)^2) := by grobner
    _ = _ := by rw [hn]; grobner

def F (b X S : Rat) := (X^2-b*S^2)*(X^2+3*b*S^2)

def Weak (b t : Rat) : Prop :=
  ∃ X S B A z : Rat, (X≠0 ∨ S≠0) ∧ (B≠0 ∨ A≠0) ∧
    z^2=(1-b*t^2)*F b X S*F b B A

def direction (b t x a m h n : Rat) : Prop :=
  let B := a*x-3*b*m
  let A := m*x+a
  let E := x*B+b*A
  let G := B+x*A
  t*(h*E+b*n*G)=h*G+n*E

def parameterEquation (b t x v w : Rat) : Prop :=
  direction b t x (1-b*(v^2+3*w^2)) (2*w) (1+b*(v^2+3*w^2)) (2*v)

private theorem square_nonneg (q : Rat) : 0≤q^2 := by
  rcases Rat.nonneg_total q with h|h
  · exact Rat.pow_nonneg h
  · have hp:=Rat.mul_nonneg h h
    rwa [show -q*(-q)=q^2 by grobner] at hp

private theorem square_zero {q : Rat} (h : q^2=0) : q=0 := by
  have hz : q*q=0 := by grobner
  exact (Rat.mul_eq_zero.mp hz).elim id id

private theorem positive_form {b : Rat} (hb : 0<b) (X S : Rat)
    (hXS : X≠0 ∨ S≠0) : 0<X^2+3*b*S^2 := by
  have hX:=square_nonneg X
  have hS:=square_nonneg S
  have hp : 0≤3*b := by grind
  have ht:=Rat.mul_nonneg hp hS
  by_cases good : 0<X^2+3*b*S^2
  · exact good
  · have e : X^2=0 := by grind
    have eS : (3*b)*S^2=0 := by grind
    have nz : 3*b≠0 := by grind
    have zS := (Rat.mul_eq_zero.mp eS).resolve_left nz
    grind [square_zero]

private theorem nonsplit (b : Rat) (hb : ∀ z : Rat, z^2≠b) (X S : Rat)
    (hXS : X≠0 ∨ S≠0) : X^2-b*S^2≠0 := by
  intro he
  by_cases hs : S=0
  · have z : X^2=0 := by rw [hs] at he; grobner
    exact hXS.elim (fun h => h (square_zero z)) (fun h => h hs)
  · have hi : S*S⁻¹=1 := by grind
    have eq : X^2=b*S^2 := by grobner
    apply hb (X*S⁻¹)
    calc (X*S⁻¹)^2 = X^2*(S⁻¹)^2 := by grobner
         _ = b := by rw [eq]; grobner

private theorem direction_scale (b t x a m h n c : Rat)
    (hd : direction b t x a m h n) :
    direction b t x (c*a) (c*m) (c*h) (c*n) := by
  unfold direction at *
  grobner

private theorem chart (b t x a m h n : Rat) (hq : h^2-b*n^2=a^2+3*b*m^2)
    (hd : direction b t x a m h n) (hs : h+a≠0) :
    ∃ v w : Rat, parameterEquation b t x v w := by
  let i := (h+a)⁻¹
  have hi : (h+a)*i=1 := by dsimp [i]; grind
  have id := quadric_parameters b (n*i) (m*i) h n a m hq
  have hp : 1+b*((n*i)^2+3*(m*i)^2)=(2*i)*h := by
    calc
      _ = i^2*((h+a)^2+b*(n^2+3*m^2)) := by grobner
      _ = _ := by rw [id.2.1]; grobner
  have hm : 1-b*((n*i)^2+3*(m*i)^2)=(2*i)*a := by
    calc
      _ = i^2*((h+a)^2-b*(n^2+3*m^2)) := by grobner
      _ = _ := by rw [id.2.2]; grobner
  refine ⟨n*i,m*i,?_⟩
  unfold parameterEquation
  rw [hp,hm,show 2*(n*i)=(2*i)*n by grobner,show 2*(m*i)=(2*i)*m by grobner]
  exact direction_scale b t x a m h n (2*i) hd

private theorem other_factor (b : Rat) (hminus : ∀ q : Rat, q^2≠ -3*b)
    (X S : Rat) (hXS : X≠0 ∨ S≠0) : X^2+3*b*S^2≠0 := by
  have h := nonsplit (-3*b) hminus X S hXS
  intro he
  apply h
  grobner

private theorem nz_mul {a b : Rat} (ha : a≠0) (hb : b≠0) : a*b≠0 :=
  fun h => (Rat.mul_eq_zero.mp h).elim ha hb

private theorem sign_chart (b a m h n : Rat) (hb : b≠0)
    (hq : h^2-b*n^2=a^2+3*b*m^2) (hk : a^2+3*b*m^2≠0) (hc : h+a=0) :
    -h+a≠0 := by
  intro opposite
  have ha : a=0 := by grind
  have hh : h=0 := by grind
  have prod : b*(n^2+3*m^2)=0 := by rw [ha,hh] at hq; grobner
  have hzero := (Rat.mul_eq_zero.mp prod).resolve_left hb
  by_cases hm : m=0
  · apply hk
    rw [ha,hm]
    grobner
  · have pos := positive_form (b:=1) (by decide) n m (Or.inr hm)
    grind

private theorem scale_slope_eq (b t x B A h n c : Rat)
    (he : t*(h*(x*B+b*A)+b*n*(B+x*A))=h*(B+x*A)+n*(x*B+b*A)) :
    t*(h*(x*(c*B)+b*(c*A))+b*n*(c*B+x*(c*A))) =
      h*(c*B+x*(c*A))+n*(x*(c*B)+b*(c*A)) := by grobner

private theorem conjugate_norm (b x B A : Rat) :
    (x*B+b*A)^2-b*(B+x*A)^2=(x^2-b)*(B^2-b*A^2) := by grobner

private theorem regroup (b t x B A : Rat) :
    (1-b*t^2)*F b x 1*F b B A=
    (1-b*t^2)*(((x^2-b)*(B^2-b*A^2))*((x^2+3*b)*(B^2+3*b*A^2))) := by
  dsimp [F]
  grobner

private theorem flip_direction (b t x a m h n : Rat) (hd : direction b t x a m h n) :
    direction b t x a m (-h) (-n) := by dsimp [direction] at *; grobner

private theorem flip_quadric (b a m h n : Rat) (hq : h^2-b*n^2=a^2+3*b*m^2) :
    (-h)^2-b*(-n)^2=a^2+3*b*m^2 := by grobner

private theorem finite_to_parameters (b t x B A z : Rat)
    (hns : ∀ q : Rat, q^2≠b) (hminus : ∀ q : Rat, q^2≠ -3*b)
    (hBA : B≠0 ∨ A≠0) (hz : z^2=(1-b*t^2)*F b x 1*F b B A) :
    ∃ v w : Rat, parameterEquation b t x v w := by
  let a:=x*B+3*b*A
  let m:=x*A-B
  let E:=x*B+b*A
  let G:=B+x*A
  let k:=(x^2+3*b)*(B^2+3*b*A^2)
  have inv := inverse_slope b x B A
  change a*x-3*b*m=(x^2+3*b)*B ∧ m*x+a=(x^2+3*b)*A ∧
      a^2+3*b*m^2=k at inv
  have ht : 1-b*t^2≠0 := by
    simpa using nonsplit b hns 1 t (Or.inl (by decide))
  have hx : x^2-b≠0 := by
    simpa only [show (1:Rat)^2=1 by decide,Rat.mul_one] using nonsplit b hns x 1 (Or.inr (by decide))
  have hB := nonsplit b hns B A hBA
  have hp : x^2+3*b≠0 := by
    simpa only [show (1:Rat)^2=1 by decide,Rat.mul_one] using other_factor b hminus x 1 (Or.inr (by decide))
  have hB' := other_factor b hminus B A hBA
  have hk : k≠0 := nz_mul hp hB'
  have hD : E^2-b*G^2=(x^2-b)*(B^2-b*A^2) := conjugate_norm b x B A
  have hnon : (E^2-b*G^2)*k≠0 := by rw [hD]; exact nz_mul (nz_mul hx hB) hk
  have hs : z^2=(1-b*t^2)*((E^2-b*G^2)*k) := by
    rw [hD,hz]
    exact regroup b t x B A
  obtain ⟨h,n,hn,he⟩ := (norm_fibre_iff b t E G k ht hnon).mp ⟨z,hs⟩
  have hq : h^2-b*n^2=a^2+3*b*m^2 := hn.trans inv.2.2.symm
  have hd : direction b t x a m h n := by
    unfold direction
    rw [inv.1,inv.2.1]
    exact scale_slope_eq b t x B A h n (x^2+3*b) he
  by_cases hc : h+a≠0
  · exact chart b t x a m h n hq hd hc
  · have hb : b≠0 := by simpa using (hns 0).symm
    have hK : a^2+3*b*m^2≠0 := by rw [inv.2.2]; exact hk
    exact chart b t x a m (-h) (-n) (flip_quadric b a m h n hq)
      (flip_direction b t x a m h n hd) (sign_chart b a m h n hb hq hK (Classical.byContradiction hc))

private theorem dehomogenize (b t X S B A z : Rat) (hs : S≠0)
    (hz : z^2=(1-b*t^2)*F b X S*F b B A) :
    ∃ x z' : Rat, z'^2=(1-b*t^2)*F b x 1*F b B A := by
  let i:=S⁻¹
  have hi : S*i=1 := by dsimp [i]; grind
  have homog : F b (X*i) (S*i)=F b X S*i^4 := by dsimp [F]; grobner
  refine ⟨X*i,z*i^2,?_⟩
  rw [hi] at homog
  rw [homog]
  calc (z*i^2)^2 = z^2*i^4 := by grobner
       _ = _ := by rw [hz]; grobner

private theorem weak_to_parameters (b t : Rat) (hns : ∀ q : Rat, q^2≠b)
    (hminus : ∀ q : Rat, q^2≠ -3*b) (hw : Weak b t) :
    ∃ x v w : Rat, parameterEquation b t x v w := by
  obtain ⟨X,S,B,A,z,hXS,hBA,hz⟩ := hw
  by_cases hs : S≠0
  · obtain ⟨x,z',hc⟩ := dehomogenize b t X S B A z hs hz
    exact ⟨x,finite_to_parameters b t x B A z' hns hminus hBA hc⟩
  · have hsz : S=0 := by grind
    by_cases ha : A≠0
    · have h' : z^2=(1-b*t^2)*F b B A*F b X S := by rw [hz]; grobner
      obtain ⟨x,z',hc⟩ := dehomogenize b t B A X S z ha h'
      exact ⟨x,finite_to_parameters b t x X S z' hns hminus hXS hc⟩
    · have haz : A=0 := by grind
      have hX : X≠0 := by grind
      have hB : B≠0 := by grind
      have hi : (X*B)*(X*B)⁻¹=1 := by
        have : X*B≠0 := by grind [Rat.mul_eq_zero]
        grind
      rw [hsz,haz] at hz
      have hm : z^2=(1-b*t^2)*(X*B)^4 := by rw [hz]; dsimp [F]; grobner
      let i:=(X*B)⁻¹
      have hi' : (X*B)*i=1 := hi
      have hsq : (z*i^2)^2=1-b*t^2 := by
        calc
          _ = z^2*i^4 := by grobner
          _ = (1-b*t^2)*((X*B)*i)^4 := by rw [hm]; grobner
          _ = _ := by rw [hi']; grobner
      let z' := (z*i^2)*F b 0 1
      have hc : z'^2=(1-b*t^2)*F b 0 1*F b 0 1 := by
        calc z'^2 = (z*i^2)^2*(F b 0 1)^2 := by dsimp [z']; grobner
             _ = _ := by rw [hsq]; grobner
      exact ⟨0,finite_to_parameters b t 0 0 1 z' hns hminus (Or.inr (by decide)) hc⟩

private theorem coefficients_nonzero (b v w : Rat) (hns : ∀ q : Rat, q^2≠b) :
    1-b*(v^2+3*w^2)≠0 ∨ 2*w≠0 := by
  by_cases hw : w=0
  · subst w
    left
    have he := nonsplit b hns 1 v (Or.inl (by decide))
    intro hc
    apply he
    grobner
  · right
    intro he
    apply hw
    grobner

private theorem image_coord (b x a m : Rat) (hk : a^2+3*b*m^2≠0) :
    a*x-3*b*m≠0 ∨ m*x+a≠0 := by
  by_cases h : a*x-3*b*m≠0
  · exact Or.inl h
  · right
    intro hz
    apply hk
    have h' : a*x-3*b*m=0 := Classical.byContradiction h
    calc a^2+3*b*m^2 = a*(m*x+a)-m*(a*x-3*b*m) := by grobner
         _ = 0 := by rw [h',hz]; grobner

private theorem forward_group (b t x B A : Rat) :
    (1-b*t^2)*(x^2-b)*(x^2+3*b)*(B^2-b*A^2)*(B^2+3*b*A^2) =
    (1-b*t^2)*F b x 1*F b B A := by unfold F; grobner

private theorem parameters_to_weak (b t x v w : Rat) (hns : ∀ q : Rat, q^2≠b)
    (hminus : ∀ q : Rat, q^2≠ -3*b) (he : parameterEquation b t x v w) :
    Weak b t := by
  let a:=1-b*(v^2+3*w^2)
  let m:=2*w
  let h:=1+b*(v^2+3*w^2)
  let n:=2*v
  let B:=a*x-3*b*m
  let A:=m*x+a
  let u:=h*(x*B+b*A)+b*n*(B+x*A)
  have hq : h^2-b*n^2=a^2+3*b*m^2 := by
    dsimp [a,m,h,n]
    grobner
  have hk := other_factor b hminus a m (coefficients_nonzero b v w hns)
  have hBA : B≠0 ∨ A≠0 := image_coord b x a m hk
  have hW := bisection_witness b t x a m h n hq he
  change ((x^2+3*b)*(1-b*t^2)*u)^2 =
    (1-b*t^2)*(x^2-b)*(x^2+3*b)*(B^2-b*A^2)*(B^2+3*b*A^2) at hW
  refine ⟨x,1,B,A,(x^2+3*b)*(1-b*t^2)*u,Or.inr (by decide),hBA,?_⟩
  exact hW.trans (forward_group b t x B A)

/-- Exact rational weak-pole image, including either twist sign and both
    projective endpoints. Both hypotheses concern constants only. -/
theorem weak_iff_parameters (b t : Rat) (hns : ∀ q : Rat, q^2≠b)
    (hminus : ∀ q : Rat, q^2≠ -3*b) :
    Weak b t ↔ ∃ x v w : Rat, parameterEquation b t x v w := by
  constructor
  · exact weak_to_parameters b t hns hminus
  · rintro ⟨x,v,w,he⟩
    exact parameters_to_weak b t x v w hns hminus he

theorem positive_weak_iff_parameters (b t : Rat) (hb : 0<b) (hns : ∀ q : Rat, q^2≠b) :
    Weak b t ↔ ∃ x v w : Rat, parameterEquation b t x v w := by
  apply weak_iff_parameters b t hns
  intro q eq
  have hn:=square_nonneg q
  grind

end WeakBisection

#print axioms WeakBisection.norm_fibre_iff
#print axioms WeakBisection.inverse_slope
#print axioms WeakBisection.quadric_parameters
#print axioms WeakBisection.bisection_witness
#print axioms WeakBisection.weak_iff_parameters
#print axioms WeakBisection.positive_weak_iff_parameters
