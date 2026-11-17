import ReductionPlaces
import TwoTripleCriterion
import OrdinaryGoodReduction
import JacobianDiscriminant

/-! The reduction support of the actual rational abelian surface used in
the effective height inequality. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.JacobianConductor
open AbelianModel BinaryCover GoodReductionCharts LocalJacobians PrimitiveParameters
open ZInQ IsDiscreteValuationRing DirectCharts RationalClusters ClusterRoots ResidueExtension
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem good_on_chart (criterion : TwoTripleGoodReduction p)
    {u : ℚ} (hu : u ∉ contactSet) (hp : 17 ≤ p) {t : ℤ_[p]} {v a : ℤ_[p]ˣ}
    (coord : Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) {m l : ℕ} (hm : 0 < m)
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p : IntegralField p)^m))
    (h : RationalReduction.conditions (RationalReduction.equation p u v a t) T l) :
    GoodReductionAt p (SixJacobian.jacobian hu) := by
  let D := sexticCompletion (polynomial p u v a t) (ddmm_sextic_regular hu v a t coord).1
  have G := chart_geometry p hu v a t coord
  let : IsProper D.hom := G.1
  let : GeometricallyIntegral D.hom := G.2.1
  let : SmoothOfRelativeDimension 1 D.hom := G.2.2
  obtain ⟨_, _, e, _, _⟩ := ddmm_smooth_completion_iso hu v a t coord
  let J := IntegralPicard.paperJacobian_baseChangeIso ℚ_[p] hu D e
  exact hasGoodReduction_of_iso p J.symm (good_chart p criterion hu hp v a t coord hm T h)

/-- The only external theorem used here is the two-triple case of DDMM
10.3(5). Each prime is dispatched on the one signed rational Jacobian. -/
theorem good_outside (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    {u : ℚ} (hu : u ∉ contactSet) :
    JacobianHeight.GoodOutside (SixJacobian.jacobian hu) (HeightBudget.conductorPrimes Mult.S_mul u) := by
  intro p inst h
  obtain ⟨hp, places⟩ := ReductionPlaces.outside_conductor hu h
  rcases places with ⟨hf, hg⟩ | ⟨k, hk, hf, _⟩ | ⟨g, hg, _, hv⟩
  · exact IntegralPicard.ordinary_goodReduction p hu (by omega) hf hg
  · obtain ⟨t, v, a, coord, T, h⟩ := RationalReduction.even_contact_chart p u hp k hk hf
    exact good_on_chart (ddmm p) hu hp coord hk T h
  · obtain ⟨t, a, coord, T, h, _⟩ := RationalReduction.pole_chart p u hp g hg hv
    exact good_on_chart (ddmm p) hu hp coord hg T h

/-- The reduction assumption at the bounded-polynomial endpoint has been
replaced by a statement about arbitrary sextics with two clusters of three. -/
theorem original_of_marking_and_periods (hF : GroupScheme ℚ → ℝ)
    (effective : JacobianHeight.EffectiveSurfaceHeight hF) (streng : JacobianHeight.StrengEstimates)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (marking : ∀ (u : ℚ) (hu : u ∉ contactSet),
      Nonempty (JacobianHeight.MarkedAction u (SixJacobian.jacobian hu)))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianHeight.JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  JacobianHeight.original_of_jacobian_geometry hF effective streng marking
    (fun _ hu => good_outside ddmm hu) periods genus rank

end
end ZInQBlueprint.JacobianConductor
#print axioms ZInQBlueprint.JacobianConductor.good_outside
#print axioms ZInQBlueprint.JacobianConductor.original_of_marking_and_periods
