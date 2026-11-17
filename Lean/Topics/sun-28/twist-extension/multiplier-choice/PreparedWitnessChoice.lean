import PartnerQuartic
import DoubleVanishing
import SingleSection
import SurfaceProjection

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.TwistRank Sun28.PreparedPoles Sun28.PairedClasses
  Sun28.PrescribedPoints Sun28.TwistExtension Sun28.GlobalSections Sun28.PointFibres
  Sun28.PointDescent Sun28.PointLifts Sun28.ScalarHeight Sun28.FixedPreparation
  Sun28.Forward Sun28.WitnessIndices Sun28.Concrete Sun28.RealCharts Sun28.CyclicOrbit
  Sun28.RealProjection ZInQ
open private admissible_nonsquare from OrbitResidual
open scoped Sun28.RealCharts
noncomputable section

private theorem norm_prepare {B:ℚ} (prep:ClassPrepared B) {m:ℤ} {b t:ℕ}
    (c:PreparedClasses B m b t) : 0<B ∧ B<(m:ℚ) := by
  obtain ⟨a,an,A⟩:=c.beta_scale
  have bp:=prep.prepare.2.1
  have pos:0<(m:ℚ)*B:=A ▸ mul_pos (by exact_mod_cast c.beta_positive) (sq_pos_of_ne_zero an)
  have mp : 0 < m :=by exact_mod_cast pos_of_mul_pos_left pos bp.le
  have one : (1:ℚ) ≤ m :=by exact_mod_cast (show 1 ≤ m by omega)
  exact ⟨bp,lt_of_lt_of_le (lt_trans prep.prepare.2.2.1 (by norm_num : (1:ℚ)/2<1)) one⟩

/-- It is enough to prove the old positive-second-class residual for those actual
prepared positions where the negative companion multiplier fails. -/
def ChoiceResidual : Prop := ∀ (B:ℚ), ClassPrepared B → ∀ (m:ℤ) (b d:ℕ),
    (m:ℚ)∈smallMultipliers → PreparedClasses B m b d →
    ∀ ν∈smallMultipliers, Partner (m:ℚ) ν →
    ¬Surface b (1-B/ν) →
    ¬FactorPair b d → ¬OneQuartic (b:ℚ) d →
    (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) d t) → ¬CancelledFactors b d →
    Surface (b:ℚ) d

private theorem positive_branch {B:ℚ} {m:ℤ} {b d:ℕ}
    (c:PreparedClasses B m b d) (surf:Surface (b:ℚ) d) :
    ∃e z,poleBranch (m:ℚ) B e z := by
  obtain ⟨a,an,A⟩:=c.beta_scale
  obtain ⟨v,vn,H⟩:=c.theta_scale
  exact (branch_iff_surface (by exact_mod_cast c.beta_positive) (by exact_mod_cast c.theta_positive.ne') an vn A H).mpr surf

theorem choice_of_sections (old : SectionResidual) : ChoiceResidual := by
  intro B ready m b d mem c ν _ _ _ nofactor noone noratio nocancel
  have a:AdmissiblePair b d:=⟨c.beta_positive,c.theta_positive,c.beta_sf,c.theta_sf,c.disjoint,
    c.beta_six,c.theta_six,c.beta_mod,c.theta_mod,c.beta_local,c.theta_local⟩
  obtain ⟨f,norm⟩:=actual_pair ready.prepare mem c
  obtain ⟨s,pos,short,_,_,rep⟩:=old b d a (ready.class_at m b d mem c) f norm nofactor noone noratio nocancel
  exact (surface_iff_single (by exact_mod_cast c.beta_positive) (by exact_mod_cast c.theta_positive.ne')).mpr
    ⟨s,pos.ne',(single_iff_represented (by exact_mod_cast c.beta_positive) (by exact_mod_cast c.theta_positive)
      pos short (admissible_nonsquare a) noone).mpr rep⟩

theorem pole_of_choice (rule:ChoiceResidual) {B:ℚ} (ready:ClassPrepared B) :
    polePredicate smallMultipliers B := by
  obtain ⟨m,b,d,mem,c⟩:=choose_classes ready.prepare
  obtain ⟨ν,member,partner⟩:=listed_partner mem
  obtain ⟨bp,short⟩:=norm_prepare ready c
  have bpos:0<(b:ℚ):=by exact_mod_cast c.beta_positive
  have dpos:0<(d:ℚ):=by exact_mod_cast c.theta_positive
  have a:AdmissiblePair b d:=⟨c.beta_positive,c.theta_positive,c.beta_sf,c.theta_sf,c.disjoint,
    c.beta_six,c.theta_six,c.beta_mod,c.theta_mod,c.beta_local,c.theta_local⟩
  by_cases hit:Surface (b:ℚ) (1-B/ν)
  · obtain ⟨u,un,A⟩:=c.beta_scale
    rcases (two_branches_iff bp short bpos un A partner).mpr (Or.inr hit) with h|h
    · exact Or.inr ⟨m,mem,h⟩
    · exact Or.inr ⟨ν,member,h⟩
  refine Or.inr ⟨(m:ℚ),mem,positive_branch c ?_⟩
  by_cases f:FactorPair b d
  · exact surface_of_factors c.beta_positive c.theta_positive f
  by_cases o:OneQuartic (b:ℚ) d
  · exact surface_of_one_quartic bpos dpos.ne' o
  by_cases r:∃ u:ℚ,u≠0 ∧ RatioCover (b:ℚ) d u
  · obtain ⟨u,un,g⟩:=r
    obtain ⟨r1,r3,r9⟩:=regular_base a u un
    exact (surface_iff_one_or_nonzero bpos dpos.ne').mpr (Or.inr (nonzero_of_ratio bpos dpos un r1 r3 r9 g))
  by_cases cancel:CancelledFactors b d
  · exact surface_of_old c.beta_positive c.theta_positive (realized_of_cancelled c.beta_positive c.theta_positive cancel)
  exact rule B ready m b d mem c ν member partner hit f o (fun u un g=>r ⟨u,un,g⟩) cancel

theorem certificate (rule:ChoiceResidual) {w x η} (h:SelectedAt w x η) :
    PointCertificate w fixedMultiplier anchor x η gamma denominator smallMultipliers smallMultipliers := by
  obtain ⟨q,hh,b,n,t,z⟩:=h.guards
  refine ⟨q,hh,b,(rational_chart_iff _).mpr n,(rational_chart_iff _).mpr t,(rational_chart_iff _).mpr z,h.scales,?_,?_⟩
  · intro j
    obtain ⟨live,p⟩:=h.ordinary j
    exact ⟨live,pole_of_choice rule p⟩
  · obtain ⟨δ,sgn,live,p⟩:=h.scalar
    exact ⟨δ,sgn,live,pole_of_choice rule p⟩

theorem integer_fibre (rule:ChoiceResidual) {X:ℤ}
    (available:∃ a:Fin 9→AffineInput,∃η:ℚ,SelectedAt (nineAffine a).doubles (X:ℚ) η) :
    ∃w:Fin 28→ℚ,Sun28.eval28 fixedPolynomial (X:ℚ) w=0 := by
  obtain ⟨a,η,h⟩:=available
  exact (polynomial_iff_certificate _).mpr ⟨a,η,certificate rule h⟩

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

theorem integer_root (classification : Sun28.RealComponents.PublishedProposition72)
    (sieve : Sun28.WeightedSelection.PositiveSurplus) (rule : ChoiceResidual) (k : ℤ) :
    ∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial (k : ℚ) w = 0 := by
  let component := Sun28.RealComponents.openComponent_of_published classification
  let orbit := of_open_component diagonalGenerator component
  let model := parameterModel_on_subgroup DiagonalClosure orbit (generator_value diagonalGenerator component)
  exact integer_fibre rule (selected_preparation orbit model
    (ray_selection (Sun28.NormSieve.pattern_iff.mpr (Sun28.WeightedSelection.prime_values_iff_surplus.mpr sieve))) k)

end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.choice_of_sections
#print axioms Sun28.MultiplierChoice.pole_of_choice
#print axioms Sun28.MultiplierChoice.certificate
#print axioms Sun28.MultiplierChoice.integer_fibre

#print axioms Sun28.MultiplierChoice.integer_root
