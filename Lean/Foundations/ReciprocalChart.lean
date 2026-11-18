module

public import Std

@[expose] public section

namespace ReciprocalChart

open Lean.Grind

/-- Eliminate an ordinate auxiliary, retaining an arbitrary factor on the numerator. -/
theorem ordinate_elimination {K : Type} [Field K] (a d N B g z T : K)
    (h : a * d ≠ 0) (hg : d * g = N) :
    (∃ k : K, (a*d)*k = -B ∧ k*z = -g*T) ↔ B*z = a*N*T := by
  have hi := Field.mul_inv_cancel h
  constructor
  · rintro ⟨k, hk, hz⟩
    calc B*z = -(((a*d)*k)*z) := by rw [hk]; grobner
         _ = -(a*d*(k*z)) := by grobner
         _ = a*(d*g)*T := by rw [hz]; grobner
         _ = _ := by rw [hg]
  · intro hz
    refine ⟨-B*(a*d)⁻¹, ?_, ?_⟩
    · calc a*d*(-B*(a*d)⁻¹) = -B*((a*d)*(a*d)⁻¹) := by grobner
           _ = -B := by rw [hi]; grobner
    · calc -B*(a*d)⁻¹*z = -(B*z)*(a*d)⁻¹ := by grobner
           _ = (-g*T)*((a*d)*(a*d)⁻¹) := by rw [hz, ←hg]; grobner
           _ = -g*T := by rw [hi]; grobner

/-- The rational anchor is homogeneous of degree two if its fixed constant also has weight one. -/
theorem anchor_rescaling (S C u v w f : Rat) :
    (S*u)^2 + 6*(S*v)^2 - 2*(S*w)^2 - 4*(S*C)*(S*w) - 3*(S*f)^2 =
      S^2 * (u^2+6*v^2-2*w^2-4*C*w-3*f^2) := by grobner

/-- The scaled squaring recurrence doubles the exponent after multiplying by the seed. -/
theorem scaled_ladder (B L : Nat) (u : Nat → Nat) (seed : u 0 = B*L)
    (step : ∀ j, u (j+1) = B * (u j)^2) (j : Nat) :
    B * u j = (B^2*L) ^ (2^j) := by
  induction j with
  | zero => rw [seed]; simp [Nat.pow_succ]; grobner
  | succ j ih =>
    calc B * u (j+1) = (B*u j)^2 := by rw [step]; grobner
         _ = ((B^2*L)^(2^j))^2 := by rw [ih]
         _ = (B^2*L)^(2^(j+1)) := by rw [←Nat.pow_mul, Nat.pow_succ 2 j]

/-- The norm node has a quadratic equation after the common denominator has been squared. -/
theorem norm_with_denominator {K : Type} [Field K] (r t z₀ z₁ B : K) (ht : t ≠ 0) :
    (∃ U V : K, t*U=z₀ ∧ t*V=z₁ ∧ B=U^2+r*V^2) ↔
      t^2*B=z₀^2+r*z₁^2 := by
  have hi := Field.mul_inv_cancel ht
  constructor
  · rintro ⟨U,V,hU,hV,hB⟩
    rw [←hU, ←hV, hB]; grobner
  · intro h
    have cancel (z : K) : t*(t⁻¹*z)=z := by
      calc t*(t⁻¹*z) = (t*t⁻¹)*z := by grobner
           _ = z := by rw [hi]; grobner
    refine ⟨t⁻¹*z₀,t⁻¹*z₁,cancel z₀,cancel z₁,?_⟩
    calc B = (t*t⁻¹)^2*B := by rw [hi]; grobner
         _ = (t⁻¹)^2*(t^2*B) := by grobner
         _ = _ := by rw [h]; grobner

/-- A retained inverse pair lets the coefficient seed use two smaller coefficients. -/
theorem guarded_seed {K : Type} [Field K] (B L u F t : K) (guard : F*t=L) :
    u-L-(B-1)*(F*t)=0 ↔ u=B*L := by
  rw [guard]
  constructor <;> intro h <;> grobner

#print axioms guarded_seed
#print axioms norm_with_denominator
#print axioms scaled_ladder
#print axioms ordinate_elimination
#print axioms anchor_rescaling
end ReciprocalChart
