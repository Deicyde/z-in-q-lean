import HPExactFiniteSum
import JacobianDimension
import SixContactAction

/-! Height and reduction hypotheses on the Picard variety of the rational paper model. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianHeight
open AbelianModel NormalDescent ZInQ
open scoped NormalDescent
noncomputable section

/-- Rational real multiplication on this actual group scheme, with the ring law
on its endomorphisms induced by the commutative group law on the Jacobian. -/
def RationalRM (A : GroupScheme ℚ) : Prop :=
  ∃ i : realOrder →+* End A, Function.Injective i

/-- The marked real multiplication over the algebraic closure and the two precise
moduli assertions needed for descent, on the actual signed Picard variety. -/
structure MarkedAction (u : ℚ) (A : GroupScheme ℚ) where
  embedding : realOrder →+* End ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj
    A)
  faithful : Function.Injective embedding
  polarized : let X := ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj
    A).X.left
    (X ⟶ X) → Prop
  labelled : IsSquare (-(27 * SixContact.J u + 16) / SixContact.J u) →
    let E := (embedding QuadraticAlgebra.omega).asHom.hom.hom.hom.left
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ a, polarized a ∧
      (deck A.X.hom σ ≫ a) ≫ E =
        E ≫ deck A.X.hom σ ≫ a
  signs : SixContact.J u * (64 * SixContact.J u - 81) * (27 * SixContact.J u + 16) ≠ 0 →
    ∀ a, polarized a → a = 𝟙 _ ∨ a = (GrpObj.inv (X :=
      ((Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj A).X)).left

/-- Smoothness and properness of this Jacobian discharge all the scheme-theoretic
hypotheses for descent. The square and excluded automorphism locus follow from the
six-contact parametrization. -/
theorem rationalRM_of_marked {u : ℚ} {hu : u ∉ contactSet} (m : MarkedAction u (SixJacobian.jacobian hu)) :
    RationalRM (SixJacobian.jacobian hu) := by
  let A := SixJacobian.jacobian hu
  let ab := SixJacobian.isAbelian hu
  let : Smooth A.X.hom := ab.smooth
  let : IsProper A.X.hom := ab.proper
  let : IsReduced A.X.left := isReduced_of_smooth_over_field (g := A.X.hom) ab.smooth
  obtain ⟨j,hj,_⟩ := six_contact_real_multiplication hu A m.embedding m.faithful
    m.polarized m.labelled m.signs
  exact ⟨j,hj.1⟩

def GoodOutside (A : GroupScheme ℚ) (S : Finset ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ∉ S → GoodReductionAt p A

/-- The real-multiplication surface case of von Känel's Theorem 6.2.
The input function is the stable Faltings height in his normalization. -/
def EffectiveSurfaceHeight (hF : GroupScheme ℚ → ℝ) : Prop :=
  ∀ (A : GroupScheme ℚ) (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p) →
    IsAbelianScheme A → SmoothOfRelativeDimension 2 A.X.hom → RationalRM A → GoodOutside A S →
    hF A ≤ (6:ℝ)^288 * (HeightBudget.primeProduct S : ℝ)^24

/-- Reduced periods at all embeddings and the published height identity for the
same rational Picard variety. This is the application still to be constructed. -/
structure JacobianPeriods (K : Type) [Field K] [NumberField K] (hF : GroupScheme ℚ → ℝ)
    {u : ℚ} (hu : u ∉ contactSet) where
  period : (K →ₐ[ℚ] ℂ) → ThetaPeriod.SiegelPeriod
  reduced : ∀ σ, InStrengDomain (period σ)
  evenNonzero : ∀ σ i, ThetaPeriod.thetaNull (period σ) (ThetaQuotient.evenIndices i) ≠ 0
  formula : (Module.finrank ℚ K : ℝ) * (hF (SixJacobian.jacobian hu) + Real.log Real.pi) =
    (Module.finrank ℚ K : ℝ) * (3 * Real.log ((SixContact.J u).num.natAbs : ℝ) +
      2 * Real.log ((SixContact.J u).den : ℝ))/60 - (∑ σ, Real.log (peterssonFactor (period σ)))/10

/-- The stable height occurring at the finite and infinite places is evaluated on the
very group scheme to which rational real multiplication and good reduction are applied. -/
theorem original_of_jacobian_geometry (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (streng : StrengEstimates)
    (marking : ∀ (u : ℚ) (hu : u ∉ contactSet), Nonempty (MarkedAction u (SixJacobian.jacobian hu)))
    (reduction : ∀ (u : ℚ) (hu : u ∉ contactSet),
      GoodOutside (SixJacobian.jacobian hu) (HeightBudget.conductorPrimes Mult.S_mul u))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget := by
  apply original_of_paper_fibre_heights streng _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨d⟩⟩ := periods u hu
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (fun h => Mult.prime_of_mem_S_mul h) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    ((marking u hu).elim rationalRM_of_marked) (reduction u hu)
  exact ⟨K,inferInstance,inferInstance,⟨⟨hF (SixJacobian.jacobian hu), d.period,
    d.reduced, d.evenNonzero, by rw [ExactFinite.finite_sum_eq K hu]; exact d.formula, upper⟩⟩⟩

end
end ZInQBlueprint.JacobianHeight
#print axioms ZInQBlueprint.JacobianHeight.RationalRM
#print axioms ZInQBlueprint.JacobianHeight.rationalRM_of_marked
#print axioms ZInQBlueprint.JacobianHeight.EffectiveSurfaceHeight
#print axioms ZInQBlueprint.JacobianHeight.JacobianPeriods
#print axioms ZInQBlueprint.JacobianHeight.GoodOutside
#print axioms ZInQBlueprint.JacobianHeight.original_of_jacobian_geometry
