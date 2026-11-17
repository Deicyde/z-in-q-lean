import AnchorInstructions

namespace AnchorCircuit
open StructuralReduction StructuralReduction.Transfer84
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate
open ProjectionFibres ProjectionFibres.Comparison ProjectionFibres.Actual EllipticHeight.Labels

theorem factor_nonzero (x : Fin 84 → Rat) : linearFactor x ≠ 0 := by
  rw [linear_wire]
  have n := norm_positive (rootH x 1)
  have j := J_ne
  grind

private theorem trace_identity (m n c d j k s t : Rat)
    (h₃ : d = 307328*j*(256*n))
    (h₄ : s*n = m) (h₅ : (t-4096*c)*(j*k)=s) :
    t*(d*k) = 256*307328*m + 4096*(d*k)*c := by grobner

theorem cleared_parameter (x : Fin 84 → Rat) :
    parameter x*(linearFactor x*H) = atWire x 305+4096*(linearFactor x*H)*firstProduct x := by
  rw [quotient_wire,product_wire]
  let h := rootH x 1
  let j := rootJ x 1
  have hn : norm (divisor h) ≠ 0 := by have := norm_positive h; grind
  have hk : J*H=(3:Rat)^1475 := (Rat.mul_comm ..).trans scale_exponents
  have nz : J*H≠0 := by have := H_ne; have := J_ne; grind
  apply trace_identity _ (norm (divisor h)) _ _ J H (shifted h j) _ (linear_wire x)
  · exact Rat.div_mul_cancel hn
  · unfold parameter
    rw [←hk]
    have rep := Rat.div_mul_cancel (a:=shifted h j) nz
    change (shifted h j/(J*H)+4096*productReal x-4096*productReal x)*(J*H)=shifted h j
    grobner

/-- Identity on the entire rational coordinate space, before imposing any circuit rows. -/
theorem literal_row (x : Fin 84 → Rat) :
    atWire x 984 = 4*(linearFactor x*H)^2 *
      conic (9*cell x 14/H) (9*cell x 15/H) (1+cell x 16/H) (parameter x) :=
  (homogeneous_row x).trans (homogeneous _ _ _ _ _ _ _ H_ne (cleared_parameter x))

theorem row_zero_iff (x : Fin 84 → Rat) :
    atWire x 984=0 ↔ conic (9*cell x 14/H) (9*cell x 15/H)
        (1+cell x 16/H) (parameter x)=0 := by
  rw [literal_row]
  have d := factor_nonzero x
  have k := H_ne
  have unit : 4*(linearFactor x*H)^2 ≠ 0 := by grind
  exact ⟨fun z => (Rat.mul_eq_zero.mp z).resolve_left unit,fun z => by rw [z,Rat.mul_zero]⟩

/-- Necessity at both primes for every active solution of the retained equations. -/
theorem denominators84 (x : Fin 84 → Rat) (marked : Bool)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0) :
    (¬ 2 ∣ (parameter x).den) ∧ (¬ 3 ∣ (parameter x).den) :=
  OrbitIdentification.Anchor.rational_conic <| (row_zero_iff x).mp
    (signed_zero x marked active zero 984 (by decide))

/-- The same conclusion from the ordinary output of the physical 80-variable polynomial. -/
theorem physical_anchor (y : Fin 80 → Rat) (zero : Binding.V y 9813=0) :
    (¬ 2 ∣ (parameter (decoded y)).den) ∧ (¬ 3 ∣ (parameter (decoded y)).den) :=
  denominators84 _ false (by simp) (ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans zero))

theorem physical_marked_anchor (y : Fin 80 → Rat) (active : y 0≠0) (zero : Binding.V y 9814=0) :
    (¬ 2 ∣ (parameter (decoded y)).den) ∧ (¬ 3 ∣ (parameter (decoded y)).den) := by
  have p := (Binding.physical_pointwise true y).symm.trans zero
  change y 0 * output80 false y=0 at p
  exact denominators84 _ false (by simp) (ordinary_decoded y ((Rat.mul_eq_zero.mp p).resolve_left active))

#print axioms norm_positive
#print axioms literal_row
#print axioms row_zero_iff
#print axioms denominators84
#print axioms physical_anchor
#print axioms physical_marked_anchor
end AnchorCircuit
