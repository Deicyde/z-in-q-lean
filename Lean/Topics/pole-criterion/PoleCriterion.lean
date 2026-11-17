import SignedPole

namespace PoleCriterion
open Lean.Grind

private theorem square_nonneg (x : Rat) : 0 ≤ x^2 := by
  rcases Rat.nonneg_total x with h|h
  · exact Rat.pow_nonneg h
  · have hn := Rat.mul_nonneg h h
    rwa [show -x*(-x)=x^2 by grobner] at hn

/-- A quadratic has a rational root precisely when its reduced discriminant
    is a square, provided it cannot be a nonzero constant. -/
theorem quadratic (A C D : Rat) (hc : A=0 → C=0 → D=0) :
    (∃ x : Rat, A*x^2+2*C*x+D=0) ↔ ∃ y : Rat, y^2=C^2-A*D := by
  constructor
  · rintro ⟨x,e⟩
    exact ⟨A*x+C,by grobner⟩
  rintro ⟨y,e⟩
  by_cases ha : A=0
  · by_cases h : C=0
    · exact ⟨0,by rw [hc ha h]; grobner⟩
    · have ci : C*C⁻¹=1 := by grind
      exact ⟨-D*C⁻¹/2,by rw [ha]; grobner⟩
  · have ai : A*A⁻¹=1 := by grind
    refine ⟨(y-C)*A⁻¹,?_⟩
    calc _ = (y^2-C^2+A*D)*A⁻¹ := by grobner
         _ = 0 := by rw [e]; grobner

private theorem det_zero (B a m h n : Rat)
    (norm : h^2-B*n^2=a^2+3*B*m^2) (det : a^2+B*m^2=0) : a=0 ∧ B*m=0 := by
  have aa := square_nonneg a
  have mm := square_nonneg m
  have hh := square_nonneg h
  have nn := square_nonneg n
  have z : a^2=0 := by
    rcases Rat.nonneg_total B with hp|hn
    · have hp' := Rat.mul_nonneg hp mm
      grind
    · have hn' := Rat.mul_nonneg hn nn
      have eq : h^2+(-B)*n^2= -2*a^2 := by grobner
      grind
  have za : a=0 := by
    have h0 : a*a=0 := by grobner
    exact (Rat.mul_eq_zero.mp h0).elim id id
  have prod : (B*m)*m=0 := by grobner
  exact ⟨za,(Rat.mul_eq_zero.mp prod).elim id (fun hm=>by rw [hm]; grobner)⟩

/-- The direction equation on the quadric never specializes to a nonzero constant. -/
theorem no_constant (B a m h n L M : Rat)
    (norm : h^2-B*n^2=a^2+3*B*m^2)
    (lead : a*L+m*M=0) (lin : a*M-B*m*L=0) : B*(a*L-3*m*M)=0 := by
  by_cases d : a^2+B*m^2=0
  · obtain ⟨ha,hm⟩ := det_zero B a m h n norm d
    grobner
  · have l : (a^2+B*m^2)*L=0 := by grobner
    have k : (a^2+B*m^2)*M=0 := by grobner
    have lz := (Rat.mul_eq_zero.mp l).resolve_left d
    have mz := (Rat.mul_eq_zero.mp k).resolve_left d
    rw [lz,mz]; grobner

/-- Squarehood of this value decides the slope equation at fixed b, v and w. -/
def discriminant (b v w : Rat) : Rat :=
  let B := 17*b
  let h := 1+B*(v^2+3*w^2)
  let K := h^2-4*B*v^2
  (289-B)*K^2+(4*B*w*(h-34*v))^2

def polynomial (b u v w : Rat) : Rat :=
  let B := 17*b
  let h := 1+B*(v^2+3*w^2)
  (h^2-4*B*v^2)*(u^2+B-289)-8*B*w*(h-34*v)*u

private theorem norm_square (B a m h n L M : Rat)
    (norm : h^2-B*n^2=a^2+3*B*m^2) (scale : M^2-B*L^2=(289-B)*(h^2-B*n^2)) :
    (a*M-B*m*L)^2-(a*L+m*M)*(B*(a*L-3*m*M)) =
    (289-B)*(h^2-B*n^2)^2+(2*B*m*L)^2 := by
  calc _ = (a^2+3*B*m^2)*(M^2-B*L^2)+(2*B*m*L)^2 := by grobner
       _ = _ := by rw [scale,←norm]; grobner

theorem square_iff (b v w : Rat) :
    (∃ x : Rat, SignedPole.polynomial b x v w=0) ↔ ∃ y : Rat, y^2=discriminant b v w := by
  let B := 17*b
  let a := 1-B*(v^2+3*w^2)
  let h := 1+B*(v^2+3*w^2)
  let m := 2*w
  let n := 2*v
  let L := h-17*n
  let M := B*n-17*h
  have norm : h^2-B*n^2=a^2+3*B*m^2 := by dsimp [h,a,m,n]; grobner
  have scale : M^2-B*L^2=(289-B)*(h^2-B*n^2) := by dsimp [L,M]; grobner
  have disc := norm_square B a m h n L M norm scale
  have de : discriminant b v w=(289-B)*(h^2-B*n^2)^2+(2*B*m*L)^2 := by
    unfold discriminant; dsimp [B,h,n,m,L]; grobner
  have poly (x : Rat) : SignedPole.polynomial b x v w =
      (a*L+m*M)*x^2+2*(a*M-B*m*L)*x+B*(a*L-3*m*M) := by
    unfold SignedPole.polynomial; dsimp [a,h,n,m,L,M,B]; grobner
  simp only [poly,de,←disc]
  exact quadratic _ _ _ (no_constant B a m h n L M norm)

/-- Completing the square a second time needs no inverse when K vanishes. -/
theorem norm_iff (K S d : Rat) :
    (∃ y : Rat, y^2=d*K^2+S^2) ↔ ∃ u : Rat, K*(u^2-d)-2*S*u=0 := by
  have h := quadratic K (-S) (-K*d) (fun hk _=>by rw [hk]; grobner)
  have p (u : Rat) : K*u^2+2*(-S)*u+(-K*d)=K*(u^2-d)-2*S*u := by grobner
  have e : (-S)^2-K*(-K*d)=d*K^2+S^2 := by grobner
  simpa only [p,e] using h.symm

theorem fibre (b v w : Rat) :
    (∃ x : Rat, SignedPole.polynomial b x v w=0) ↔ ∃ u : Rat, polynomial b u v w=0 := by
  apply (square_iff b v w).trans
  unfold discriminant polynomial
  let B := 17*b
  let h := 1+B*(v^2+3*w^2)
  let K := h^2-4*B*v^2
  have p (u : Rat) : K*(u^2-(289-B))-2*(4*B*w*(h-34*v))*u=
      K*(u^2+B-289)-8*B*w*(h-34*v)*u := by grobner
  simpa only [p] using norm_iff K (4*B*w*(h-34*v)) (289-B)

theorem exact (b : Rat) : WitnessTransfer.FixedZero.PsiZero b ↔
    ∃ u v w : Rat, polynomial b u v w=0 := by
  rw [SignedPole.exact]
  constructor
  · rintro ⟨x,v,w,h⟩
    obtain ⟨u,e⟩ := (fibre b v w).mp ⟨x,h⟩
    exact ⟨u,v,w,e⟩
  · rintro ⟨u,v,w,h⟩
    obtain ⟨x,e⟩ := (fibre b v w).mpr ⟨u,h⟩
    exact ⟨x,v,w,e⟩

/-- Integer coefficients in the original input, after rescaling the witnesses. -/
def integral (b u v w : Rat) : Rat :=
  let H := 17+b*(v^2+3*w^2)
  (H^2-68*b*v^2)*(17*u^2+b-17)-136*b*u*w*(H-34*v)

theorem rescale (b u v w : Rat) :
    integral b u v w = 17*polynomial b (17*u) (v/17) (w/17) := by
  unfold integral polynomial
  grobner

theorem integral_exact (b : Rat) : WitnessTransfer.FixedZero.PsiZero b ↔
    ∃ u v w : Rat, integral b u v w=0 := by
  rw [exact]
  constructor
  · rintro ⟨u,v,w,h⟩
    refine ⟨u/17,17*v,17*w,?_⟩
    rw [rescale,show 17*(u/17)=u by grobner,show 17*v/17=v by grobner,
      show 17*w/17=w by grobner,h]; grobner
  · rintro ⟨u,v,w,h⟩
    rw [rescale] at h
    exact ⟨17*u,v/17,w/17,by grobner⟩

end PoleCriterion
#print axioms PoleCriterion.quadratic
#print axioms PoleCriterion.no_constant
#print axioms PoleCriterion.square_iff
#print axioms PoleCriterion.norm_iff
#print axioms PoleCriterion.fibre
#print axioms PoleCriterion.exact

#print axioms PoleCriterion.rescale
#print axioms PoleCriterion.integral_exact
