import ThomaeBranchPoints
import ThetaParity

/-! The square of the absolute invariant suffices for the six-contact height.
The single unreplayed polynomial identification on the branch side is visible
as a separate hypothesis, independently checked over rational function fields. -/
namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient SexticThetaHeight SexticInvariants Polynomial
noncomputable section

theorem ratHeight_neg (j : ℚ) : ZInQ.ratHeight (-j) = ZInQ.ratHeight j := by
  simp [ZInQ.ratHeight,Rat.neg_num,Rat.neg_den]

theorem height_of_absolute {z : Tuple} (ha : ∀ i, IsAlgebraic ℚ (chart z i)) (hp : pct z ≠ 0)
    {j : ℚ} (hj : j ≠ 0) (hi : absInvariant z = 3779136/(j:ℂ)) :
    ZInQ.ratHeight j ≤ 40*chartHeight z ha := by
  let K := fieldOf (chart z)
  let _ := numberField (chart z) ha
  let φ : K →+* ℂ := (fieldOf (chart z)).val.toRingHom
  let x := coordinates (chart z)
  have hprod : (∏ i, φ (x (evenIndices i))) ≠ 0 := chart_nondegenerate hp
  have abs : (∑ i, φ (x (evenIndices i))^8)^5 / (∏ i, φ (x (evenIndices i)))^4 =
      3779136 / φ (j:K) := by
    change absInvariant (chart z) = _
    rw [invariant_chart hp,hi,map_ratCast]
  obtain ⟨hd,he⟩ := IgusaRatio.quotient_of_absolute (z := x ∘ evenIndices)
    (by exact_mod_cast hj : (j : K) ≠ 0) hprod abs
  exact ratHeight_le_level_two_exact x j he hd

theorem height_of_squared_absolute {z : Tuple} (ha : ∀ i, IsAlgebraic ℚ (chart z i))
    (hp : pct z ≠ 0) {j : ℚ} (hj : j ≠ 0) (hi : absInvariant z^2 = (3779136/(j:ℂ))^2) :
    ZInQ.ratHeight j ≤ 40*chartHeight z ha := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with h | h
  · exact height_of_absolute ha hp hj h
  · rw [← ratHeight_neg j]
    exact height_of_absolute ha hp (neg_ne_zero.mpr hj) (by simpa [div_neg] using h)

/-- Data all refer to one labelled sextic and a single genus-two period.
The root calculation below is independent of the period and of the homology labels. -/
structure ThomaePeriodData (u δ : ℚ) (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) where
  matrix : SiegelPeriod
  roots : Fin 6 → ℂ
  distinct : Function.Injective roots
  root : ∀ i, aeval (roots i) (sextic u δ) = 0
  label : Fin 10 ≃ Partition
  scale : ℂˣ
  thomae : ∀ i, thetaNull matrix (evenIndices i)^8 =
    (scale:ℂ)*branchValue (finiteBranches roots) (label i)
  branchInvariant : (∑ i, branchValue (finiteBranches roots) (label i))^10 /
    (∏ i, branchValue (finiteBranches roots) (label i)) =
      (((igusaI4 (sextic u δ)^5/(sextic u δ).discr^2 : ℚ) : ℂ))^2
  stable : ℝ
  comparison : let e := of_sextic_thomae hu hδ roots distinct root label scale thomae (thetaNull_odd matrix)
    let h := chartHeight (thetaNull matrix) (eighth_ratios_algebraic e)
    |max 1 h - max 1 (stable + Real.log Real.pi)/2| ≤ ThetaMetric.pazukiConstant *
      Real.log (min (max 1 h) (max 1 (stable + Real.log Real.pi)) + 2)
  reduction : stable ≤ HeightBudget.vonKaenelBudget u

def eighthData {u δ : ℚ} {hu : u ∉ ZInQ.contactSet} {hδ : δ ≠ 0}
    (p : ThomaePeriodData u δ hu hδ) : EighthPowerData (thetaNull p.matrix) :=
  of_sextic_thomae hu hδ p.roots p.distinct p.root p.label p.scale p.thomae (thetaNull_odd p.matrix)

theorem thomae_height {u δ : ℚ} {hu : u ∉ ZInQ.contactSet} {hδ : δ ≠ 0}
    (p : ThomaePeriodData u δ hu hδ) : ZInQ.ratHeight (SixContact.J u) ≤
      40*chartHeight (thetaNull p.matrix) (eighth_ratios_algebraic (eighthData p)) := by
  apply height_of_squared_absolute _ (eighth_even_nonzero (eighthData p))
    (CoarseConic.unmarked_range hu).2.ne
  rw [eighth_absolute_square (eighthData p)]
  exact p.branchInvariant.trans (by rw [invariant hu hδ]; push_cast; rfl)

def HasThomaePeriods : Prop := ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet),
  ∃ (δ : ℚ) (hδ : δ ≠ 0), Nonempty (ThomaePeriodData u δ hu hδ)

theorem remaining_of_thomaePeriods (hp : HasThomaePeriods) : HeightBudget.RemainingComparisons := by
  intro u hu
  obtain ⟨δ,hδ,⟨p⟩⟩ := hp u hu
  let h := chartHeight (thetaNull p.matrix) (eighth_ratios_algebraic (eighthData p))
  refine ⟨h,(thomae_height p).trans (by linarith),?_⟩
  have h₁ := ThetaMetric.theta_le h p.stable p.comparison
  have h₂ := max_le_max_left 1 p.reduction
  have h₃ := le_max_left (1:ℝ) (HeightBudget.vonKaenelBudget u)
  linarith

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.ratHeight_neg
#print axioms ZInQBlueprint.ThetaPeriod.height_of_squared_absolute
#print axioms ZInQBlueprint.ThetaPeriod.thomae_height
#print axioms ZInQBlueprint.ThetaPeriod.remaining_of_thomaePeriods
