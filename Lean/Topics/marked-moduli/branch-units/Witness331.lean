import UniformUnitObstruction

/-! Contact, invariant and discriminant valuations at the concrete parameter 331². -/
open Polynomial
namespace ZInQBlueprint.BranchHeight.UnitObstruction
open SexticThetaHeight
noncomputable section
private instance : Fact (Nat.Prime 331) := ⟨by norm_num⟩
abbrev witness : ℚ := parameterAt 331

theorem contact_values (c : ℚ) (hc : c ∈ ZInQ.contactSet) :
    padicValRat 331 (witness-c) = if c=0 then 2 else 0 :=
  contact_valuations (by decide) c hc

theorem outside_support (S : Finset ℕ) : ¬331 ∣ ZInQ.contactSupport S witness :=
  uniform_outside_support (by decide) S

theorem J_and_coefficient_valuations :
    padicValRat 331 (SixContact.J witness) = 4 ∧ padicValRat 331 (3779136:ℚ) = 0 :=
  uniform_valuations (by decide)

theorem rootClass_valuations :
    padicValRat 331 (rootClass₁ witness) = 0 ∧
    padicValRat 331 (rootClass₂ witness) = 2 ∧
    padicValRat 331 (rootClass₃ witness) = 2 := by
  -- The prime divides the zero contact difference to order two and is a unit at the other five.
  have units := radicand_scalar_units (p:=331) (by decide)
  have h0 : padicValRat 331 witness = 2 := by simpa using contact_values 0 (by norm_num [ZInQ.contactSet])
  have h15 := contact_values (-15) (by norm_num [ZInQ.contactSet])
  have h20 := contact_values (-20) (by norm_num [ZInQ.contactSet])
  have h24 := contact_values (-24) (by norm_num [ZInQ.contactSet])
  have h30 := contact_values (-30) (by norm_num [ZInQ.contactSet])
  have h60 := contact_values (-60) (by norm_num [ZInQ.contactSet])
  simp only [sub_neg_eq_add,neg_eq_zero,OfNat.ofNat_ne_zero,ite_false] at h15 h20 h24 h30 h60
  unfold rootClass₁ rootClass₂ rootClass₃
  repeat rw [padicValRat.mul (by norm_num [witness,parameterAt]) (by norm_num [witness,parameterAt])]
  rw [units.1,units.2.1,units.2.2,h0,h15,h20,h24,h30,h60]
  norm_num

theorem factor_valuations :
    padicValRat 331 ((firstFactor witness).discr) = -4 ∧
    padicValRat 331 ((secondFactor witness).discr) = -2 ∧
    padicValRat 331 ((thirdFactor witness).discr) = 2 := by
  obtain ⟨d₁,d₂,d₃⟩ := factor_discriminants (unmarked_at (p:=331))
  obtain ⟨h₁,h₂,h₃⟩ := rootClass_valuations
  rw [d₁,d₂,d₃]
  repeat rw [padicValRat.mul (by norm_num [witness,parameterAt,rootClass₁,rootClass₂,rootClass₃])
    (by norm_num [witness,parameterAt,rootClass₁,rootClass₂,rootClass₃])]
  simp only [padicValRat.pow,h₁,h₂,h₃]
  have h0 : padicValRat 331 witness = 2 := by simpa using contact_values 0 (by norm_num [ZInQ.contactSet])
  have h20 := contact_values (-20) (by norm_num [ZInQ.contactSet])
  have h30 := contact_values (-30) (by norm_num [ZInQ.contactSet])
  simp only [sub_neg_eq_add,neg_eq_zero,OfNat.ofNat_ne_zero,ite_false] at h20 h30
  have unit (a:ℕ) (hu : ¬331 ∣ a) : padicValRat 331 (a:ℚ)=0 := by simp [padicValNat.eq_zero_of_not_dvd hu]
  have h2 : padicValRat 331 2 = 0 := unit 2 (by decide)
  have h3 : padicValRat 331 3 = 0 := unit 3 (by decide)
  have h4 : padicValRat 331 4 = 0 := unit 4 (by decide)
  repeat rw [padicValRat.div (by norm_num [witness,parameterAt]) (by norm_num [witness,parameterAt])]
  repeat rw [padicValRat.mul (by norm_num [witness,parameterAt]) (by norm_num [witness,parameterAt])]
  rw [h0,h20,h30,h2,h3,h4,padicValRat.one]
  norm_num

end
end ZInQBlueprint.BranchHeight.UnitObstruction
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.contact_values
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.outside_support
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.J_and_coefficient_valuations
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.rootClass_valuations
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.factor_valuations
