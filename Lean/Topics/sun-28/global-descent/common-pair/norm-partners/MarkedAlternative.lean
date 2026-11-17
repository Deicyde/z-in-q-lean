import CompanionExclusion
import PointPeriodProjection

namespace Sun28.NormPartners
open Sun28 Sun28.SelmerRealization Sun28.SeededPartners Sun28.PairedClasses Sun28.GlobalSections
open Sun28.TwistRank Sun28.TwistExtension Sun28.PrescribedPoints Sun28.PointFibres
open Sun28.PreparedPoles Sun28.GlobalDescent Sun28.PointLifts
open Sun28.QualitativeRows Sun28.MultiplierChoice Sun28.Concrete Sun28.RealCharts
open Sun28.CyclicOrbit Sun28.RealProjection ZInQ
open ZInQBlueprint.FiveMetric ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods ZInQBlueprint.IntegralSections
noncomputable section

/-- A strict point with square x-l lies on precisely the old ordered cover. -/
theorem cover_of_square_difference {b l : ℕ} (bp : 0<b) {u y : ℚ} (un : u≠0) (yn : y≠0)
    (curve : y^2=((b:ℚ)*u^2)*(b*u^2-l)*(b*u^2+3*l))
    (diff : IsSquare ((b:ℚ)*u^2-l)) : Cover ℚ l b 1 := by
  obtain ⟨v,hv⟩ := diff
  have bp' : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  have vn : v≠0 := by
    rintro rfl
    rw [hv] at curve
    simp [yn] at curve
  let w := y/((b:ℚ)*u*v)
  have h : (b:ℚ)*u^2+3*l=b*w^2 := by
    dsimp [w]
    field_simp [bp',un,vn]
    rw [hv] at curve
    linear_combination -curve
  refine ⟨u,v,w,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩
  · push_cast; linear_combination hv
  · push_cast; linear_combination -h

theorem necessary_nonsquare {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (excluded : ¬CancelledFactors b d) {u y : ℚ} (un : u≠0) (yn : y≠0)
    (H : y^2=((b:ℚ)*u^2)*(b*u^2-(b*q*d:ℕ))*(b*u^2+3*(b*q*d:ℕ))) :
    ¬ IsSquare ((b:ℚ)*u^2-(b*q*d:ℕ)) :=
  fun h => all_companions_fail ad excluded C (cover_of_square_difference ad.1 un yn H h)

/-- It suffices for a single seeded companion to carry a nonzero rational
point with squareclass b as abscissa. The missing second label is free. -/
def WeakCompanion : Prop :=
  ∀ b d : ℕ, Residual b d → ∃ q, Candidate b d q ∧ strictPoint b ((b*q)*d)

theorem companion_implies_weak (H : CompanionLift) : WeakCompanion :=
  fun b d residual => ((companion_iff_no_residual.mp H) ⟨b,d,residual⟩).elim

theorem sections_of_weak_companion (H : WeakCompanion) : RemainingSections := by
  intro b d ad inp fixed norm factors out ratios cancelled
  obtain ⟨q,C,strict⟩ := H b d ⟨ad,inp,fixed,norm,factors,out,ratios,cancelled⟩
  obtain ⟨u,y,un,yn,first⟩ := strict_of_family ad.1 C.nontrivial
    (Nat.squarefree_mul_iff.mp C.squarefree).2.2 (candidate_quartics ad C).1
  obtain ⟨v,z,vn,zn,second⟩ := strict
  have pos : 0 < b*q := Nat.mul_pos ad.1 (by have := C.nontrivial;omega)
  have pair : NonzeroPair (b:ℚ) (d:ℚ) := ⟨(b*q:ℕ),u,v,y,z,by exact_mod_cast pos.ne',un,vn,yn,zn,
    first,by simpa only [Nat.cast_mul] using second⟩
  have sur := (surface_iff_one_or_nonzero (by exact_mod_cast ad.1) (by exact_mod_cast ad.2.1.ne')).mpr (Or.inr pair)
  obtain ⟨s,pos,short,allowed,v,marked⟩ := reduced_ratio ad out sur
  exact ⟨s,pos,short,allowed,v,Sun28.CommonPair.orbit_excluded ad out pos short v,marked⟩

set_option maxRecDepth 14000
set_option exponentiation.threshold 250
theorem integer_of_weak_companion {k : ℤ} (w : Window k) (row : PointRow w) (H : WeakCompanion) :
    ∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial (k:ℚ) v=0 := by
  have sections := sections_iff_descent.mpr (remaining_sections_iff.mp (sections_of_weak_companion H))
  exact (compiled_one_sign _).mpr (integer_fibre (choice_of_sections sections) (selected_of_point w row))

theorem one_sign_of_weak_companion (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72)
    (rows : ∀ k, PointRow (integerWindow realCurves k)) (H : WeakCompanion) (x : ℚ) :
    (∃ v : Fin 28 → ℚ, eval28 oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  constructor
  · intro root
    have marked : MarkedFibres (210^300) 128 :=
      marked_fibres_of_pencil (by norm_num) (pencil_fibres_of_evaluations fibres)
    exact WitnessHeight.integral_of_two_loci (WitnessHeight.two_loci_of_uniform
      (original_height_of_quotients (marked_quotients table marked))) x ((compiled_one_sign x).mp root)
  · rintro ⟨k,rfl⟩
    exact integer_of_weak_companion _ (rows k) H

end
end Sun28.NormPartners

#print axioms Sun28.NormPartners.cover_of_square_difference
#print axioms Sun28.NormPartners.necessary_nonsquare
#print axioms Sun28.NormPartners.companion_implies_weak
#print axioms Sun28.NormPartners.sections_of_weak_companion
#print axioms Sun28.NormPartners.integer_of_weak_companion
#print axioms Sun28.NormPartners.one_sign_of_weak_companion
