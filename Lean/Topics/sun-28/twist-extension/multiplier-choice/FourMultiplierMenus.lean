import PreparedWitnessChoice
import PositiveMultiplierMenu
import ScalarSignChoice

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.TwistRank Sun28.TwistExtension Sun28.ScalarHeight
  Sun28.FixedPreparation Sun28.Forward Sun28.WitnessIndices Sun28.Concrete ZInQ

noncomputable section

/-- All thirty-two positive multipliers and the alternative second twist ratio. -/
def PositiveMenu (B : ℚ) : Prop := ∃ μ ∈ smallMultipliers, 0 < μ ∧
  ∃ ν ∈ smallMultipliers, Partner μ ν ∧
    (Surface (μ*B) (1-B/μ) ∨ Surface (μ*B) (1-B/ν))

def ordinaryArgument (w : NinePoints) (x η : ℚ) (j : Fin 3) : ℚ :=
  let A := (pointScale w fixedMultiplier j)^2
  let t := A*η
  detector A t / (ordinaryTraceAt w fixedMultiplier anchor (beta x) A t)^2

def scalarArgument (w : NinePoints) (x : ℚ) : ℚ :=
  let r := scalarRadicand (beta x)
  signedValue r 1 gamma denominator (scalarTree r (scalarEntries w fixedMultiplier))

/-- All four values use the very same nine doubled points and the same slope. -/
def FourMenus (w : NinePoints) (x η : ℚ) : Prop :=
  (∀ j, PositiveMenu (ordinaryArgument w x η j)) ∧ PositiveMenu |scalarArgument w x|

private theorem absolute_pole (B : ℚ) :
    polePredicate smallMultipliers |B| ↔ polePredicate smallMultipliers B := by
  rcases le_or_gt 0 B with pos|neg
  · rw [abs_of_nonneg pos]
  · rw [abs_of_neg neg]; exact neg_pole B

private theorem scalar_interval {w x η} (h : SelectedAt w x η) :
    0 < |scalarArgument w x| ∧ |scalarArgument w x| < 1/2 := by
  obtain ⟨δ,sgn,_,p⟩ := h.scalar
  have interval : 0 < signedValue (scalarRadicand (beta x)) δ gamma denominator
      (scalarTree (scalarRadicand (beta x)) (scalarEntries w fixedMultiplier)) ∧
      signedValue (scalarRadicand (beta x)) δ gamma denominator
        (scalarTree (scalarRadicand (beta x)) (scalarEntries w fixedMultiplier)) < 1/2 :=
    ⟨p.prepare.2.1,p.prepare.2.2.1⟩
  rcases sgn with rfl|rfl
  · change 0 < scalarArgument w x ∧ scalarArgument w x < 1/2 at interval
    rwa [abs_of_pos interval.1]
  · have eq (r W:ℚ) : signedValue r (-1) gamma denominator W = -signedValue r 1 gamma denominator W := by
      simp [signedValue]
    rw [eq] at interval
    change 0 < -scalarArgument w x ∧ -scalarArgument w x < 1/2 at interval
    rwa [abs_of_neg (neg_pos.mp interval.1)]

theorem selected_certificate_iff {w x η} (s : SelectedAt w x η) :
    PointCertificate w fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers ↔
      FourMenus w x η := by
  have ordinary (j : Fin 3) :
      ordinaryAccepted w fixedMultiplier anchor (beta x) ((pointScale w fixedMultiplier j)^2)
        ((pointScale w fixedMultiplier j)^2*η) smallMultipliers ↔ PositiveMenu (ordinaryArgument w x η j) := by
    obtain ⟨nz,p⟩ := s.ordinary j
    exact ⟨fun o => (pole_iff_positive_menu p.prepare.2.1 p.prepare.2.2.1).mp o.2,
      fun m => ⟨nz,(pole_iff_positive_menu p.prepare.2.1 p.prepare.2.2.1).mpr m⟩⟩
  obtain ⟨_,_,wn,_⟩ := s.scalar
  obtain ⟨pos,small⟩ := scalar_interval s
  have sc : scalarAccepted w fixedMultiplier (scalarRadicand (beta x)) gamma denominator smallMultipliers ↔
      PositiveMenu |scalarArgument w x| := by
    rw [scalar_sign]
    exact ⟨fun o => (pole_iff_positive_menu pos small).mp ((absolute_pole _).mpr o.2),
      fun m => ⟨wn,(absolute_pole _).mp ((pole_iff_positive_menu pos small).mpr m)⟩⟩
  constructor
  · intro p
    exact ⟨fun j => (ordinary j).mp (p.ordinary j),sc.mp p.scalar⟩
  · rintro ⟨o,c⟩
    obtain ⟨q,h,b,n,t,z⟩ := s.guards
    exact ⟨q,h,b,(rational_chart_iff _).mpr n,(rational_chart_iff _).mpr t,(rational_chart_iff _).mpr z,
      s.scales,fun j => (ordinary j).mpr (o j),sc.mpr c⟩

/-- It suffices to find one common prepared nine-point comparison for each
integer, with one positive menu choice for each of its four rational values. -/
theorem root_of_selected_menus {k : ℤ}
    (available : ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (k:ℚ) η ∧
      FourMenus (nineAffine a).doubles (k:ℚ) η) :
    ∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial (k:ℚ) w=0 := by
  obtain ⟨a,η,s,m⟩ := available
  exact (polynomial_iff_certificate _).mpr ⟨a,η,(selected_certificate_iff s).mpr m⟩
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.selected_certificate_iff
#print axioms Sun28.MultiplierChoice.root_of_selected_menus
