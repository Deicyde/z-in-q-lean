import PhysicalScalar

namespace StructuralReduction
open BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
set_option maxRecDepth 4096

/-- Small exact tests include cancellation at equal order, sign, a nontrivial
reduction of the denominator, and the exceptional normalization at 17. -/
theorem exact_order_controls :
    order 7 (-3/49)= -2 ∧ order 7 ((1/7:Rat)+48/7)=1 ∧
    order 7 (301/17)=1 ∧ order 17 (-3/17)= -1 ∧ order 17 (34/34)=0 := by decide +kernel

theorem endpoint_controls :
    ThreeCoordinates.Sextic (17*(301/17)) (289-17*(301/17)) ∧
    ThreeCoordinates.Sextic (17*(-3/17)) (289-17*(-3/17)) ∧
    ThreeCoordinates.Sextic 0 289 ∧ ThreeCoordinates.Sextic 289 0 :=
  ⟨⟨0,0,2,by decide +kernel⟩,⟨0,1,0,by decide +kernel⟩,⟨0,0,0,by decide +kernel⟩,⟨0,0,0,by decide +kernel⟩⟩

theorem excluded_controls :
    ¬ThreeCoordinates.Sextic (17*(1/5)) (289-17*(1/5)) ∧
    ¬ThreeCoordinates.Sextic (17*1) (289-17*1) := by
  constructor
  · intro h
    have hp : Prime 5 := prime_of_finite (by decide +kernel) (by decide +kernel)
    have v := good_prime_positive hp (by decide +kernel) (by decide +kernel) (b:=(1/5:Rat)) (by decide +kernel)
      ⟨-1,by decide +kernel⟩ h
    exact (by decide +kernel : ¬0<order 5 (1/5)) v
  · intro h
    have v:=seventeen_even_positive (b:=1) (by decide +kernel) ⟨0,by decide +kernel⟩ h
    exact (by decide +kernel : ¬0<order 17 1) v

/-- The additive rational group with its ordinary parameter instantiates the tangent
interface; the independent native control evaluates the elliptic group itself. -/
def additiveChart {p : Nat} (hp : Prime p) : MultiplicationChart p (rationalPlace hp) Rat where
  formal := fun _=>True
  z := id
  origin := rfl
  tangent := by
    intro n a _ _ _ _
    refine ⟨trivial,0,fun nz => False.elim (nz rfl),?_⟩
    rw [Ring.zsmul_eq_intCast_mul];dsimp only [id];grobner

theorem signed_multiple_control :
    order 7 ((-98:Rat)*49)=4 := by
  let hp : Prime 7 := prime_of_finite (by decide +kernel) (by decide +kernel)
  have e:=((additiveChart hp).multiple hp (Q:=49) (a:= -98) (by decide +kernel) trivial (by decide +kernel)
    (by decide +kernel)).2.2
  change order 7 ((-98:Int) • (49:Rat))=order 7 49+order 7 (-98) at e
  rw [Ring.zsmul_eq_intCast_mul] at e
  exact e.trans (by decide +kernel)

end StructuralReduction
