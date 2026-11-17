import PhysicalAnchor
import InertCoordinates
import DyadicCoefficients

namespace AnchorCircuit
set_option maxRecDepth 8192
open BinaryQuartic StructuralReduction StructuralReduction.Transfer84
open PhysicalProjection.Comparison ProjectionFibres ProjectionFibres.Actual EllipticHeight.Labels
open ProgressionWitnesses.SingleContact

private theorem integral_of_den {p : Nat} {x : Rat} (h : ¬p∣x.den) : 0≤order p x := by
  have d : natOrder p x.den=0 := by rw [natOrder,dif_neg (fun e=>h e.2.2)]
  unfold order
  rw [d]
  omega

/-- Removing an integral summand preserves integrality. -/
private theorem other_integral (v : RationalOrder) {a b : Rat} (bn : b≠0)
    (ha : a=0 ∨ 0≤v.ord a) (hab : 0≤v.ord (a+b)) : 0≤v.ord b := by
  by_cases az : a=0
  · simpa only [az,Rat.zero_add] using hab
  have av:=ha.resolve_left az
  apply Int.le_of_not_gt
  intro neg
  have cmp:=v.addUnequal a b az bn (by omega)
  rw [cmp.2] at hab
  omega

private theorem read_orders (g c : Rat) (d : Fin 4 → Nat) (k : Nat)
    (den₂ : ¬2∣(g/3^1475+4096*c).den) (den₃ : ¬3∣(g/3^1475+4096*c).den)
    (cc : c≠0 ∧ order 2 (4096*c)= -2*((d 0:Int)+d 1+d 2+d 3))
    (dyadic : ¬2∣g.den)
    (triadic : (∀ i, d i=0) → (¬3∣c.den) ∧ g≠0 ∧ order 3 g=(k:Int)+1) :
    (∀ i, d i=0) ∧ 1474≤k := by
  let pow : Rat := 3^1475
  have pn : pow≠0 := by decide +kernel
  have prm₂ : Prime 2 := prime_of_finite (by decide) (by decide)
  have prm₃ : Prime 3 := StructuralHeights.prime3
  let v₂ := primeOrder 2 prm₂
  let v₃ := primeOrder 3 prm₃
  have t₂ : 0≤v₂.ord (g/pow+4096*c) := integral_of_den den₂
  have t₃ : 0≤v₃.ord (g/pow+4096*c) := integral_of_den den₃
  have scale₂ : v₂.ord pow=0 := by
    have h : v₂.ord 3=0 := order_nat_unit (n:=3) prm₂ (by decide)
    have e := (power_order v₂ (by decide : (3:Rat)≠0) 1475).2
    change v₂.ord ((3:Rat)^1475)=0
    rw [e,h]; decide
  have gv : g/pow=0 ∨ 0≤v₂.ord (g/pow) := by
    by_cases gz : g=0
    · exact Or.inl (by rw [gz,Rat.div_def,Rat.zero_mul])
    · apply Or.inr
      rw [v₂.div _ _ gz pn,scale₂]
      rw [Int.sub_zero]
      exact integral_of_den dyadic
  have cn : 4096*c≠0 := fun h=>(Rat.mul_eq_zero.mp h).elim (by decide) cc.1
  have sum := other_integral v₂ cn gv t₂
  change 0≤order 2 (4096*c) at sum
  rw [cc.2] at sum
  have odd (i : Fin 4) : d i=0 := by
    have branches : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases branches with rfl|rfl|rfl|rfl <;> omega
  refine ⟨odd,?_⟩
  obtain ⟨cden,gn,go⟩ := triadic odd
  change g≠0 at gn
  change v₃.ord g=(k:Int)+1 at go
  have scale₃ := (power_order v₃ (by decide : (3:Rat)≠0) 1475).2
  have base₃ : v₃.ord 3=1 := order_prime prm₃
  change v₃.ord pow=(1475:Int)*v₃.ord 3 at scale₃
  rw [base₃] at scale₃
  have nz : g/pow≠0 := fun h=>gn (by have e := Rat.div_mul_cancel (a:=g) pn; rw [h,Rat.zero_mul] at e; exact e.symm)
  have cint : 0≤v₃.ord c := integral_of_den cden
  have unit : v₃.ord 4096=0 := order_nat_unit (n:=4096) prm₃ (by decide)
  have cg : 0≤v₃.ord (4096*c) := by rw [v₃.mul _ _ (by decide) cc.1,unit,Int.zero_add]; exact cint
  rw [Rat.add_comm] at t₃
  have bound := other_integral v₃ nz (Or.inr cg) t₃
  rw [v₃.div _ _ gn pn,scale₃,go] at bound
  omega

/-- Read the index constraints from the physical denominator theorem once the
    reciprocal-abscissa orders at the two primes have been specialized. -/
theorem physical_index_orders {y : Fin 80 → Rat} (zero : Binding.V y 9813=0)
    (d : Fin 4 → Nat) (k : Nat)
    (four : ∀ i, order 2 (norm (sq (rootH (decoded y) i)))= -6-4*(d i:Int))
    (dyadic : ¬2∣(shifted (rootH (decoded y) 1) (rootJ (decoded y) 1)).den)
    (triadic : (∀ i, d i=0) →
      (¬3∣(productReal (decoded y)).den) ∧
      shifted (rootH (decoded y) 1) (rootJ (decoded y) 1)≠0 ∧
      order 3 (shifted (rootH (decoded y) 1) (rootJ (decoded y) 1))=(k:Int)+1) :
    (∀ i, d i=0) ∧ 1474≤k := by
  have live (i : Fin 4) : norm (sq (rootH (decoded y) i))≠0 := by
    intro h
    have e := four i
    rw [h,show order 2 0=0 by decide +kernel] at e
    omega
  have cc := AnchorCollision.Dyadic.four_abscissas (live 0) (live 1) (live 2) (live 3)
    (four 0) (four 1) (four 2) (four 3)
  obtain ⟨den₂,den₃⟩ := physical_anchor y zero
  exact read_orders _ _ d k den₂ den₃ cc dyadic triadic

#print axioms physical_index_orders
end AnchorCircuit
