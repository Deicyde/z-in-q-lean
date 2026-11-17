import NumeratorEndpoint
import PrimitiveDouble
namespace EllipticHeight
open QuadraticInt PhysicalProjection.Comparison

private theorem denominator_live {b f : R} (hb : b≠(0,0)) (hf : f≠(0,0)) : mul b f≠(0,0) := by
  have live (x : R) (nz : x≠(0,0)) : PhysicalProjection.Comparison.norm (rational x)≠0 := by
    intro dead
    obtain ⟨u,v⟩:=(CircuitTransport.Quadratic.norm_zero_iff _ _).mp dead
    apply nz
    apply rational_injective
    exact Prod.ext u v
  intro z
  have h:=congrArg (fun w => PhysicalProjection.Comparison.norm (rational w)) z
  dsimp only at h
  rw [show PhysicalProjection.Comparison.norm (rational (0,0))=0 by dsimp [PhysicalProjection.Comparison.norm,rational]; grobner] at h
  rw [rational_mul,norm_product] at h
  exact (Rat.mul_eq_zero.mp h).elim (live b hb) (live f hf)

theorem multiply_fractions {z t : Q2} {a b e f : R} (h : represents z a b) (k : represents t e f) :
    represents (times z t) (mul a e) (mul b f) := by
  refine ⟨denominator_live h.1 k.1,?_⟩
  rw [rational_mul,rational_mul,←h.2,←k.2]
  apply Prod.ext <;> dsimp [times] <;> grobner

/-- Numerator or denominator of the product of the three unselected factors. -/
def otherThree (v : Fin 4 → R) (i : Fin 4) :=
  match i with
  | 0 => mul (mul (v 1) (v 2)) (v 3)
  | 1 => mul (mul (v 0) (v 2)) (v 3)
  | 2 => mul (mul (v 0) (v 1)) (v 3)
  | _ => mul (mul (v 0) (v 1)) (v 2)

theorem rest_fraction {x : Fin 84→Rat} {a b : Fin 4→R}
    (rows : ∀ i, represents (roots x i) (a i) (b i)) (j : Fin 4) :
    represents (rest x j) (otherThree a j) (otherThree b j) := by
  match j with
  | 0 => exact multiply_fractions (multiply_fractions (rows 1) (rows 2)) (rows 3)
  | 1 => exact multiply_fractions (multiply_fractions (rows 0) (rows 2)) (rows 3)
  | 2 => exact multiply_fractions (multiply_fractions (rows 0) (rows 1)) (rows 3)
  | 3 => exact multiply_fractions (multiply_fractions (rows 0) (rows 1)) (rows 2)


private theorem coprime_divisor {a b d : R} (h : coprime a b) (div : divides d b) : coprime a d := by
  obtain ⟨u,v,bez⟩:=h
  obtain ⟨t,ht⟩:=div
  refine ⟨u,mul t v,?_⟩
  have eq : mul d (mul t v)=mul (mul d t) v := by
    apply Prod.ext <;> dsimp [mul] <;> grobner
  rw [eq,←ht]
  exact bez

/-- The abscissa numerator on a primitive signed chart is Bézout-coprime to
both exceptional factors of the discriminant. -/
theorem exceptional_coprime {a b c : R} (pr : coprime a b) (h : chart a b c) :
    coprime (QuadraticInt.sq a) rho ∧ coprime (QuadraticInt.sq a) QuadraticInt.delta := by
  have state:=Primitive.start pr (dyadic_denominator h) (no_seven_numerator pr h)
  exact ⟨coprime_divisor state.1 state.2.1,state.2.2⟩

end EllipticHeight
#print axioms EllipticHeight.multiply_fractions
#print axioms EllipticHeight.rest_fraction
#print axioms EllipticHeight.exceptional_coprime
