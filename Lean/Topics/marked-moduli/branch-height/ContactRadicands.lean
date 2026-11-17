import QuadraticDiscriminants
import FourContactValuations

/-! The three quadratic square classes at primes outside the marked contact support. -/
namespace ZInQBlueprint.BranchHeight
noncomputable section
open ZInQ

theorem rootClasses_even {p : ℕ} [Fact p.Prime] {S : Finset ℕ} {u : ℚ}
    (hu : u ∉ contactSet) (hp : 5 < p) (hS : p ∉ S) (hout : ¬p ∣ contactSupport S u) :
    Even (padicValRat p (rootClass₁ u)) ∧ Even (padicValRat p (rootClass₂ u)) ∧
      Even (padicValRat p (rootClass₃ u)) := by
  have marks (c : Fin 4 → ℚ) (hc : ∀ i, c i ∈ contactSet) {a : ℚ} (ha : a ≠ 0)
      (hv : padicValRat p a = 0) := even_scaled_four_contact_product hu hS hout c hc ha hv
  have h₁ := marks ![-15,-20,-30,-60] (by intro i; fin_cases i <;> norm_num [contactSet])
    (a:=6) (by norm_num) ((radicand_scalar_units hp).1)
  have h₂ := marks ![0,-15,-24,-30] (by intro i; fin_cases i <;> norm_num [contactSet])
    (a:=10) (by norm_num) ((radicand_scalar_units hp).2.1)
  have h₃ := marks ![0,-20,-24,-60] (by intro i; fin_cases i <;> norm_num [contactSet])
    (a:= -15) (by norm_num) ((radicand_scalar_units hp).2.2)
  simpa [rootClass₁,rootClass₂,rootClass₃,Fin.prod_univ_succ,mul_assoc] using And.intro h₁ (And.intro h₂ h₃)

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.rootClasses_even
