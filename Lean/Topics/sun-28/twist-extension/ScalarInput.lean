import SourceFacts
import PreparedProjection

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses TwistRank ScalarHeight ContactFactors
noncomputable section
set_option maxRecDepth 8192

theorem scalar_zero_input : InputClass 526361 ∧ Squarefree (526361:ℕ) := by
  have sf : Squarefree (526361:ℕ) := by
    rw [show (526361:ℕ)=11*(109*439) by decide]
    apply (Nat.squarefree_mul (by decide : Nat.Coprime 11 (109*439))).mpr
    refine ⟨(show Nat.Prime 11 by decide).squarefree,
      (Nat.squarefree_mul (by decide : Nat.Coprime 109 439)).mpr
        ⟨(show Nat.Prime 109 by norm_num).squarefree,(show Nat.Prime 439 by norm_num).squarefree⟩⟩
  refine ⟨Or.inr ⟨0,15,by decide,by decide,?_⟩,sf⟩
  have val : integerRadicand 0 = -31581660 := by decide
  rw [val]
  symm
  apply ZInQ.RouteK.sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sf) (t:=(30:ℚ)) (by norm_num)
  norm_num

/-- The scalar input X=0 with the listed multiplier 15 has this first
squareclass. The second squareclasses in this theorem are free outputs. -/
theorem scalar_zero_products :
    InputClass 526361 ∧ ∃ d : ℕ, 1<d ∧ ∀ B : ℕ, ∃ e : ℕ, B<d*e ∧ 1<e ∧
      d.Coprime e ∧ AdmissiblePair 526361 (d*e) ∧ FixedSquares (d*e) ∧ NormConic 526361 (d*e) ∧
      FactorPair 526361 (d*e) ∧ AffineSurface (526361:ℚ) ((d*e:ℕ):ℚ) ∧ ¬(526361*d).Coprime (d*e) := by
  exact ⟨scalar_zero_input.1,prepared_products (by decide) scalar_zero_input.2 (by decide) (by decide)⟩

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.scalar_zero_input
#print axioms Sun28.TwistExtension.scalar_zero_products
