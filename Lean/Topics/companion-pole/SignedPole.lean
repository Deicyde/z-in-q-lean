import Bisection
import FixedZero

namespace SignedPole
open Lean.Grind WeakBisection

private abbrev t : Rat := 1/17
private def θ (b : Rat) := 1-b*t^2
private theorem scale (b : Rat) : 289*θ b=289-b := by unfold θ t; grobner

private theorem nonsplit {b X S : Rat} (hb : ∀ q : Rat, q^2 ≠ b) (hs : S ≠ 0) :
    X^2-b*S^2 ≠ 0 := by
  intro eq
  have inv : S*S⁻¹=1 := by grind
  apply hb (X*S⁻¹)
  calc
    (X*S⁻¹)^2 = (b*S^2)*(S⁻¹)^2 := by grobner
    _ = b := by grobner

private theorem projective_of_sextic (b : Rat) (hb : b≠0)
    (w : ThreeCoordinates.Sextic b (289-b)) : Weak b t := by
  obtain ⟨x,s,J,eq⟩ := w
  let f := F b x 1
  have row : J^2*f=(289-b)*(b-s^2)*(b+3*s^2) := by dsimp [f,F]; grobner
  have far : F b b s=b^2*((b-s^2)*(b+3*s^2)) := by unfold F; grobner
  refine ⟨x,1,b,s,J*f*b/17,Or.inr (by decide),Or.inl hb,?_⟩
  change (J*f*b/17)^2=θ b*f*F b b s
  rw [far]
  calc
    _ = (J^2*f)*(f*b^2/289) := by grobner
    _ = _ := by rw [row, ←scale b]; grobner

private theorem cancel_four (r c d B i : Rat) (unit : B*i=1) :
    r*((c*d)*B^4)*i^4=r*c*d := by
  calc r*((c*d)*B^4)*i^4 = r*c*d*(B*i)^4 := by grobner
       _ = _ := by rw [unit]; grobner

private theorem finite_chart {b X S B A z : Rat}
    (hn : ∀ q : Rat, q^2 ≠ b) (hm : ∀ q : Rat, q^2 ≠ -3*b)
    (hs : S≠0) (hB : B≠0) (eq : z^2=θ b*F b X S*F b B A) :
    ThreeCoordinates.Sextic b (289-b) := by
  have f1 := nonsplit (X:=X) hn hs
  have f2 := nonsplit (X:=X) hm hs
  have nz : F b X S≠0 := by unfold F; grind
  have si : S*S⁻¹=1 := by grind
  have bi : B*B⁻¹=1 := by grind
  have fi : (F b X S)*(F b X S)⁻¹=1 := by grind
  let u := X*S⁻¹
  let v := b*A*B⁻¹
  have ef : (u^2-b)*(u^2+3*b)*S^4=F b X S := by dsimp [u,F]; grobner
  have eg : (b-v^2)*(b+3*v^2)*B^4=b^2*F b B A := by dsimp [v,F]; grobner
  let j := 17*b*z*S^2*(B⁻¹)^2*(F b X S)⁻¹
  refine ⟨u,v,j,?_⟩
  calc
    j^2*(u^2-b)*(u^2+3*b)
        = 289*b^2*z^2*((u^2-b)*(u^2+3*b)*S^4)*(B⁻¹)^4*((F b X S)⁻¹)^2 := by
            dsimp [j]; grobner
    _ = 289*θ b*(b^2*F b B A)*(B⁻¹)^4 := by rw [ef,eq]; grobner
    _ = (289-b)*(b-v^2)*(b+3*v^2) := by rw [scale,←eg]; exact cancel_four _ _ _ _ _ bi

private theorem equal_ends {b z weight : Rat} (hw : weight≠0)
    (eq : z^2=θ b*weight^2) : ThreeCoordinates.Sextic b (289-b) := by
  have wi : weight*weight⁻¹=1 := by grind
  have sq : (z*weight⁻¹)^2=θ b := by
    calc
      _ = z^2*(weight⁻¹)^2 := by grobner
      _ = _ := by rw [eq]; grobner
  refine ⟨1,b,17*b*(z*weight⁻¹),?_⟩
  calc
    _ = 289*(z*weight⁻¹)^2*b^2*((1-b)*(1+3*b)) := by grobner
    _ = _ := by rw [sq,scale]; grobner

private theorem sextic_of_projective (b : Rat)
    (hn : ∀ q : Rat, q^2 ≠ b) (hm : ∀ q : Rat, q^2 ≠ -3*b)
    (w : Weak b t) : ThreeCoordinates.Sextic b (289-b) := by
  obtain ⟨X,S,B,A,z,first,second,eq⟩ := w
  change z^2=θ b*F b X S*F b B A at eq
  have swap : z^2=θ b*F b B A*F b X S := by grobner
  have nb : b≠0 := fun h => hn 0 (by rw [h]; decide)
  by_cases hS : S=0
  · have hX := first.resolve_right (fun n => n hS)
    by_cases hA : A=0
    · have hB := second.resolve_right (fun n => n hA)
      apply equal_ends (weight:=X^2*B^2) (z:=z) (by grind)
      subst S; subst A; unfold F at eq; grobner
    · exact finite_chart hn hm hA hX swap
  · by_cases hB : B=0
    · have hA := second.resolve_left (fun n => n hB)
      by_cases hX : X=0
      · apply equal_ends (weight:=3*b^2*S^2*A^2) (z:=z) (by grind)
        subst X; subst B; unfold F at eq; grobner
      · exact finite_chart hn hm hA hX swap
    · exact finite_chart hn hm hS hB eq

/-- The two projective endpoints are included for either sign of b. -/
theorem source_projective (b : Rat) (hn : ∀ q : Rat, q^2 ≠ 17*b)
    (hm : ∀ q : Rat, q^2 ≠ -3*(17*b)) :
    WitnessTransfer.FixedZero.PsiZero b ↔ Weak (17*b) (1/17) := by
  rw [WitnessTransfer.FixedZero.exact_sextic]
  change ThreeCoordinates.Sextic (17*b) (289-17*b) ↔ Weak (17*b) t
  exact ⟨projective_of_sextic _ (fun eq=>hn 0 (by rw [eq]; decide)),sextic_of_projective _ hn hm⟩

private theorem square_case (q : Rat) :
    ∃ x v w : Rat, parameterEquation (q^2) t x v w := by
  by_cases h : q=0
  · subst q; exact ⟨0,0,0,by unfold parameterEquation direction; grobner⟩
  have qi : q*q⁻¹=1 := by grind
  have zero : 1-q^2*((q⁻¹)^2+3*0^2)=0 := by grobner
  refine ⟨0,q⁻¹,0,?_⟩
  unfold parameterEquation
  rw [zero]; unfold direction; grobner

private theorem signed_case (b q : Rat) (e : q^2= -3*b) (nq : q≠0) :
    ∃ x v w : Rat, parameterEquation b t x v w := by
  have qi : q*q⁻¹=1 := by grind
  have zero : 1+b*(0^2+3*(q⁻¹)^2)=0 := by
    calc _ = 1-(-3*b)*(q⁻¹)^2 := by grobner
         _ = 0 := by rw [←e]; grobner
  refine ⟨0,0,q⁻¹,?_⟩
  unfold parameterEquation
  rw [zero]; unfold direction; grobner

/-- The degree-eight integer polynomial, presented in factored form. -/
def polynomial (b x v w : Rat) : Rat :=
  let B := 17*b
  let a := 1-B*(v^2+3*w^2)
  let m := 2*w
  let h := 1+B*(v^2+3*w^2)
  let n := 2*v
  let e := a*(x^2+B)-2*B*m*x
  let g := m*(x^2-3*B)+2*a*x
  (h-17*n)*e+(B*n-17*h)*g

private theorem polynomial_zero (b x v w : Rat) :
    parameterEquation (17*b) t x v w ↔ polynomial b x v w=0 := by
  unfold parameterEquation direction t polynomial
  constructor <;> intro h <;> grobner

/-- The original fixed-zero row for every rational b, including both singular
    squareclasses, is the projection of a single quadratic in x. -/
theorem exact (b : Rat) :
    WitnessTransfer.FixedZero.PsiZero b ↔ ∃ x v w : Rat, polynomial b x v w=0 := by
  have getEq : (∃ x v w : Rat, parameterEquation (17*b) t x v w) ↔
      ∃ x v w : Rat, polynomial b x v w=0 := by
    constructor
    · rintro ⟨x,v,w,h⟩; exact ⟨x,v,w,(polynomial_zero b x v w).mp h⟩
    · rintro ⟨x,v,w,h⟩; exact ⟨x,v,w,(polynomial_zero b x v w).mpr h⟩
  apply Iff.trans _ getEq
  by_cases hs : ∃ q : Rat, q^2=17*b
  · obtain ⟨q,eq⟩ := hs
    have left := (WitnessTransfer.FixedZero.exact_sextic b).mpr
      ⟨0,q,0,by rw [←eq]; grobner⟩
    have right := square_case q
    rw [eq] at right
    exact ⟨fun _=>right,fun _=>left⟩
  by_cases hm : ∃ q : Rat, q^2= -3*(17*b)
  · obtain ⟨q,eq⟩ := hm
    have nq : q≠0 := fun h=>hs ⟨0,by rw [h] at eq; grobner⟩
    have root : 17*b= -3*(q/3)^2 := by grobner
    have left := (WitnessTransfer.FixedZero.exact_sextic b).mpr
      ⟨0,q/3,0,by rw [root]; grobner⟩
    exact ⟨fun _=>signed_case _ q eq nq,fun _=>left⟩
  have hn := fun q eq=>hs (Exists.intro q eq)
  have hminus := fun q eq=>hm (Exists.intro q eq)
  exact (source_projective b hn hminus).trans (weak_iff_parameters _ _ hn hminus)

/-- Every rational first slope supplies the square used by the local sieve,
    including when the leading coefficient vanishes. -/
theorem parameter_square (B t x v w : Rat) (solution : parameterEquation B t x v w) :
    let a := 1-B*(v^2+3*w^2)
    let m := 2*w
    let h := 1+B*(v^2+3*w^2)
    let n := 2*v
    let K := a^2+3*B*m^2
    ∃ y : Rat, y^2=(1-B*t^2)*K^2+(2*B*m*(t*h-n))^2 := by
  intro a m h n K
  let L := t*h-n
  let M := B*t*n-h
  let c2 := a*L+m*M
  let c1 := a*M-B*m*L
  let c0 := B*(a*L-3*m*M)
  have norm : h^2-B*n^2=K := by dsimp [K,a,m,h,n]; grobner
  have scaled : M^2-B*L^2=(1-B*t^2)*K := by
    rw [←norm]; dsimp [M,L]; grobner
  have disc : c1^2-c2*c0=(1-B*t^2)*K^2+(2*B*m*L)^2 := by
    calc
      _ = K*(M^2-B*L^2)+(2*B*m*L)^2 := by dsimp [c1,c2,c0,K]; grobner
      _ = _ := by rw [scaled]; grobner
  have equation : c2*x^2+2*c1*x+c0=0 := by
    change direction B t x a m h n at solution
    unfold direction at solution
    dsimp [c2,c1,c0,L,M]
    grobner
  refine ⟨c2*x+c1,?_⟩
  change (c2*x+c1)^2=(1-B*t^2)*K^2+(2*B*m*L)^2
  rw [←disc]
  calc (c2*x+c1)^2 = (c1^2-c2*c0)+c2*(c2*x^2+2*c1*x+c0) := by grobner
       _ = _ := by rw [equation]; grobner

end SignedPole
#print axioms SignedPole.source_projective
#print axioms SignedPole.exact
#print axioms SignedPole.parameter_square
