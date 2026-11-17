import RationalSectionSpecialization
import GenericObstruction
import PrescribedDoubleRoot

namespace Sun28.PointConstruction
open Filter RatFunc Sun28.Ordinary Sun28.ScalarHeight Sun28.PrescribedPoints
noncomputable section
set_option maxRecDepth 8192

/-- The exact first squareclass at the prepared scalar input X=0. -/
def inputB (u:ℚ) : ℚ := 7895415*u^2

/-- A transverse sequence testing any proposed rational formula. -/
def transverse (n:ℕ) : ℚ := (109:ℚ)⁻¹ ^ (n+1)

private instance : Fact (Nat.Prime 109) := ⟨by decide⟩

theorem transverse_order (n:ℕ) : padicValRat 109 (inputB (transverse n)) = -2*(n:ℤ)-1 := by
  have val : padicValRat 109 7895415 = 1 := by
    change padicValRat 109 ((7895415:ℕ):ℚ)=1
    rw [padicValRat.of_nat];decide +kernel
  rw [inputB,transverse,padicValRat.mul (by norm_num) (pow_ne_zero 2 (pow_ne_zero _ (by norm_num))),
    val,padicValRat.pow,padicValRat.pow,padicValRat.inv]
  have p : padicValRat 109 (109:ℚ)=1 := padicValRat.self (by decide : 1<109)
  rw [p];push_cast;ring

theorem no_transverse_pole (n:ℕ) : ¬polePredicate smallMultipliers (inputB (transverse n)) := by
  intro ok
  have units : ∀ m∈smallMultipliers,padicValRat 109 m=0 := by decide +kernel
  have odd : Odd (padicValRat 109 (inputB (transverse n))) := by
    rw [transverse_order];exact ⟨-(n:ℤ)-1,by ring⟩
  have nonneg := polePredicate_sound (by decide : 3<109) smallMultipliers units ok odd
  rw [transverse_order] at nonneg
  omega

private theorem distinct : Function.Injective transverse := by
  intro n m h
  have e : padicValRat 109 (inputB (transverse n))=padicValRat 109 (inputB (transverse m)) := by rw [h]
  rw [transverse_order,transverse_order] at e
  omega

abbrev genericB : Functions := RatFunc.C (7895415:ℚ) * RatFunc.X^2

private theorem input_germ : evaluate genericB = (↑inputB:Germs) := by
  rw [map_mul,map_pow,evaluate_constant,evaluate_variable]
  rfl

/-- An identity in the four proposed witness functions would specialize to
valid rational pole witnesses for all rational inputs outside a finite set. -/
theorem specialize_branch {m:ℚ} {e z:Functions}
    (h:functionBranch (RatFunc.C m) genericB e z) :
    ∀ᶠ x:ℚ in cofinite, poleBranch m (inputB x) (value e x) (value z x) := by
  let B:=genericB
  let A:=RatFunc.C m*B
  let H:=A*(A-B^2)
  obtain ⟨guard,y,v,h1,h2⟩:=h
  change A*e*H*z≠0 at guard
  change y^2=A*(A-e)*(A+3*e) at h1
  change v^2=A*(A*z^2-e*H)*(A*z^2+3*(e*H)) at h2
  let a (x:ℚ):=m*inputB x
  let k (x:ℚ):=a x*(a x-(inputB x)^2)
  have ax:evaluate A=(↑a:Germs) := by dsimp only [A,B];rw [map_mul,evaluate_constant,input_germ];rfl
  have hk:evaluate H=(↑k:Germs) := by dsimp only [H,B];rw [map_mul,map_sub,map_pow,ax,input_germ];rfl
  have base : (value (A*e*H*z)) =ᶠ[cofinite] (fun x => a x*value e x*k x*value z x) := by
    apply Germ.coe_eq.mp
    change evaluate (A*e*H*z) = _
    rw [map_mul,map_mul,map_mul,ax,hk];rfl
  have first:=congrArg evaluate h1
  simp only [ax,map_pow,map_mul,map_sub,map_add,map_ofNat] at first
  have hfirst : (fun x => (value y x)^2) =ᶠ[cofinite] (fun x => a x*(a x-value e x)*(a x+3*value e x)) :=
    Germ.coe_eq.mp first
  have second:=congrArg evaluate h2
  simp only [map_pow,map_mul,map_sub,map_add,map_ofNat,ax,hk] at second
  have hsecond : (fun x => (value v x)^2) =ᶠ[cofinite]
      (fun x => a x*(a x*(value z x)^2-value e x*k x)*(a x*(value z x)^2+3*(value e x*k x))) :=
    Germ.coe_eq.mp second
  filter_upwards [eventually_nonzero guard,base,hfirst,hsecond] with x nz eq p q
  refine ⟨eq ▸ nz,value y x,value v x,p,?_⟩
  change _=a x*(a x*(value z x)^2-value e x*k x)*(a x*(value z x)^2+3*value e x*k x)
  simpa only [mul_assoc] using q

theorem no_scalar_function_branch {m:ℚ} (mem:m∈smallMultipliers) :
    ¬ ∃e z:Functions, functionBranch (RatFunc.C m) genericB e z := by
  rintro ⟨e,z,h⟩
  have ev:=distinct.tendsto_cofinite.eventually (specialize_branch h)
  obtain ⟨n,ok⟩ := ev.exists
  exact no_transverse_pole n (Or.inr ⟨m,mem,_,_,ok⟩)

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.transverse_order
#print axioms Sun28.PointConstruction.no_transverse_pole
#print axioms Sun28.PointConstruction.specialize_branch
#print axioms Sun28.PointConstruction.no_scalar_function_branch
