import SelectedPreparation
import SieveProjection

namespace Sun28.TwistRank
open ZInQ Ordinary Forward ScalarHeight WitnessIndices FixedPreparation Concrete
open PreparedPoles PairedClasses RealProjection RealCharts CyclicOrbit
open scoped RealCharts
noncomputable section

/-- Only the classes reached by Sun's fixed preparation need the shared
rational-point assertion. A point of its associated norm conic is supplied. -/
def LocalResidual : Prop := ∀ β θ : ℕ, AdmissiblePair β θ → InputClass β → FixedSquares θ →
  NormConic β θ → θ≠1 → ¬Family β θ → ¬SquareSection β θ → Common β θ

theorem residual_implies (old : PairedClasses.Residual) : LocalResidual := by
  intro β θ adm _ _ _ live fam _
  obtain ⟨hb,ht,sb,st,bt,b6,t6,bm,tm,bp,tp⟩ := adm
  exact old β θ hb ht sb st bt b6 t6 bm tm bp tp live fam

theorem pole_of_local_residual (rest : LocalResidual) {B : ℚ} (h : ClassPrepared B) :
    polePredicate smallMultipliers B := by
  obtain ⟨m,β,θ,member,c⟩ := choose_classes h.prepare
  obtain ⟨loc,conic⟩ := actual_pair h.prepare member c
  have points : Realized β θ := by
    by_cases eq : θ=1
    · rw [eq]; exact diagonal c.beta_positive c.beta_sf c.beta_six
    by_cases f : Family β θ
    · exact realized_of_family c.beta_positive c.theta_positive c.beta_sf
        (c.beta_six.mul_right c.disjoint) f
    by_cases sec : SquareSection β θ
    · exact realized_of_section c.beta_positive c.beta_sf (c.beta_six.mul_right c.disjoint) sec
    exact (realized_iff_common c.beta_positive c.theta_positive).mpr
      (rest β θ ⟨c.beta_positive,c.theta_positive,c.beta_sf,c.theta_sf,c.disjoint,c.beta_six,
        c.theta_six,c.beta_mod,c.theta_mod,c.beta_local,c.theta_local⟩ (h.class_at m β θ member c) loc conic eq f sec)
  obtain ⟨n,hn,_,_,first,second⟩ := points
  obtain ⟨a,an,A⟩ := c.beta_scale
  obtain ⟨d,dn,H⟩ := c.theta_scale
  have live : (m:ℚ)*B≠0 := by rw [A]; exact mul_ne_zero (by exact_mod_cast c.beta_positive.ne') (pow_ne_zero _ an)
  have nonempty : ((m:ℚ)*B)*((m:ℚ)*B-B^2)≠0 := by
    rw [H];exact mul_ne_zero (by exact_mod_cast c.theta_positive.ne') (pow_ne_zero _ dn)
  exact Or.inr ⟨m,member,branch_of_twist_points hn an dn live A H nonempty first second⟩

theorem certificate (rest : LocalResidual) {w x η} (h : SelectedAt w x η) :
    PointCertificate w fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers := by
  obtain ⟨q,hh,b,n,t,z⟩ := h.guards
  refine ⟨q,hh,b,(rational_chart_iff _).2 n,(rational_chart_iff _).2 t,(rational_chart_iff _).2 z,h.scales,?_,?_⟩
  · intro j
    obtain ⟨live,p⟩ := h.ordinary j
    exact ⟨live,pole_of_local_residual rest p⟩
  · obtain ⟨δ,sgn,nz,p⟩ := h.scalar
    exact ⟨δ,sgn,nz,pole_of_local_residual rest p⟩

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

theorem fixed_projection (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (rest : LocalResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  refine ⟨integral_of_root units ((SieveProjection.least_iff_sextic units).mpr height),?_⟩
  rintro ⟨k,rfl⟩
  let component := RealComponents.openComponent_of_published classification
  let orbit := of_open_component diagonalGenerator component
  let model := parameterModel_on_subgroup DiagonalClosure orbit (generator_value diagonalGenerator component)
  have prep := selected_preparation orbit model
    (ray_selection (NormSieve.pattern_iff.mpr (WeightedSelection.prime_values_iff_surplus.mpr sieve)))
  obtain ⟨a,η,data⟩ := prep k
  exact (polynomial_iff_certificate _).2 ⟨a,η,certificate rest data⟩

theorem integer_definition_28 (classification : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (height : FiveDescent.TwistHeight glazerConstant24)
    (sieve : WeightedSelection.PositiveSurplus) (rest : LocalResidual) : IntegerDefinition28 :=
  ⟨Concrete.fixedPolynomial,fixed_projection classification units height sieve rest⟩

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.residual_implies
#print axioms Sun28.TwistRank.pole_of_local_residual
#print axioms Sun28.TwistRank.certificate
#print axioms Sun28.TwistRank.fixed_projection
#print axioms Sun28.TwistRank.integer_definition_28
