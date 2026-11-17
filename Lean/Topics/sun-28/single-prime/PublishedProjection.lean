import MiddleRange
import PreparedProjection
import PublishedDeep

namespace Sun28.SinglePrime
open Sun28.ContactSieve Sun28.WeightedSelection Sun28.Ordinary Sun28.HeightFibres Sun28.HeightFibres.Sharp
noncomputable section

structure MiddleBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (K : ℕ) (σ C : ℝ),2810≤K ∧ (∀ p∈T,p≤K) ∧ (∀ p∈κ.primeFactors,p≤K) ∧
    0<σ ∧ 0≤C ∧ ∀ L : ℕ,K≤L → CountThreshold A d H Y T κ K L σ ∧ MiddleRow A d H Y T κ L C

def MiddleInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ p∈T,p.Prime) → 2∈T →
      ∀ H Y : ℝ,MiddleBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem positive_surplus (input : MiddleInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K,σ,C,big,inT,inAux,sp,_,est⟩:=(input X c q n roots d κ T dp kp primes two H Y).estimates
  obtain ⟨m,hm⟩:=exists_nat_gt (8*C/σ)
  let L:=max K m
  have kl : K≤L := le_max_left ..
  have ml : m≤L := le_max_right ..
  have lp : 0<(L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have step : C/(L:ℝ)<σ/8 := by
    have h := (div_lt_iff₀ sp).mp (hm.trans_le (by exact_mod_cast ml : (m:ℝ)≤L))
    apply (div_lt_iff₀ lp).mpr;nlinarith only [h]
  exact ⟨L,middle_surplus (est L kl).1 (est L kl).2 big kl inT inAux sp step⟩

/-- Integer projection from two elliptic and unit inputs, three classical height inputs,
and the remaining three project-specific arithmetic assertions. -/
theorem projection_of_residuals (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (characters : QuadraticCharacterDiscriminants)
    (height : Deep) (counts : MiddleInputs) (points : TwistRank.LocalResidual) (x : ℚ) :
    (∃ w : Fin 28→ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) := by
  have original := (original_iff_published_deep units pell regulator characters).mpr height
  exact TwistRank.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp original)
    (positive_surplus counts) points x

theorem integer_definition_from_residuals (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (characters : QuadraticCharacterDiscriminants)
    (height : Deep) (counts : MiddleInputs) (points : TwistRank.LocalResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,projection_of_residuals realCurves units pell regulator characters height counts points⟩

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.positive_surplus
#print axioms Sun28.SinglePrime.projection_of_residuals
#print axioms Sun28.SinglePrime.integer_definition_from_residuals
