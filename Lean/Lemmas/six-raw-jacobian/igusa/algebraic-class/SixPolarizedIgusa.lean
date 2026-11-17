import RationalMestre
import SixIgusaTuple
import OddEquation

/-! The geometric, principally polarized Jacobian classified by an arithmetic
Igusa tuple. The comparison uses the pointed Picard determinant on any smooth
proper genus-two model over the algebraic closure. -/
open CategoryTheory AlgebraicGeometry Polynomial
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover AbelianModel NormalDescent QuaternionLift GeometricMarking SixAbelMap
open ThetaClass QuaternionMarking CanonicalTheta JacobianHeight SexticInvariants RosatiSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Use the identity as the distinguished endomorphism to forget all
markings while retaining the polarization modulo algebraic equivalence. -/
def polarizedLabel (A : GroupScheme Qbar) (L : A.X.left.Modules) : RealLabel :=
  ⟨A,L,End.of (𝟙 A)⟩

theorem polarizedClass_eq {A B : GroupScheme Qbar} {L : A.X.left.Modules} {N : B.X.left.Modules} :
    moduliClass (polarizedLabel A L) = moduliClass (polarizedLabel B N) ↔
      ∃ e : A ≅ B, Compatible e L N := by
  rw [class_eq]
  constructor
  · rintro ⟨e,_,p⟩
    exact ⟨e,p⟩
  · rintro ⟨e,p⟩
    refine ⟨e,?_,p⟩
    change 𝟙 A ≫ e.hom = e.hom ≫ 𝟙 B
    simp

def forgetOrder : ModuliClass → ModuliClass :=
  Quotient.map (fun a => polarizedLabel a.surface a.line) (by
    intro a b equivalent
    obtain ⟨e,_,p⟩ := equivalent
    exact class_eq.mp (polarizedClass_eq.mpr ⟨e,p⟩))

@[ext] structure IgusaCoordinates where
  j2 : ℚ
  j4 : ℚ
  j6 : ℚ
  j8 : ℚ
  j10 : ℚ

def IgusaCoordinates.ofSextic (f : ℚ[X]) : IgusaCoordinates :=
  ⟨igusaJ2 f,igusaJ4 f,igusaJ6 f,igusaJ8 f,igusaJ10 f⟩

def IgusaCoordinates.scale (b : ℚ) (v : IgusaCoordinates) : IgusaCoordinates :=
  ⟨b*v.j2,b^2*v.j4,b^3*v.j6,b^4*v.j8,b^5*v.j10⟩

def bgCoordinates (j : ℚ) : IgusaCoordinates :=
  let a := 12*(j+1)
  let b := 6*(j^2+j+1)
  let c := 4*(j^3-2*j^2+1)
  ⟨a,b,c,(a*c-b^2)/4,j^3⟩

theorem signed_coordinates {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ b ≠ 0, IgusaCoordinates.ofSextic (paper ℚ u false) =
      (bgCoordinates (SixContact.J u)).scale b := by
  obtain ⟨b,hb,h₂,h₄,h₆,h₈,h₁₀⟩ := signed_igusa_tuple hu
  exact ⟨b,hb,IgusaCoordinates.ext h₂ h₄ h₆ h₈ h₁₀⟩

/-- Igusa classification followed by the canonical polarized Jacobian. The
equation is arbitrary, the open immersion specifies its smooth proper model,
and the canonical polarization is the pointed Picard determinant. -/
def PolarizedIgusaClassification (read : IgusaCoordinates → ModuliClass) : Prop :=
  ∀ (f : ℚ[X]), f.natDegree = 6 → f.Separable →
    ∀ (D : Over (Spec (.of Qbar))) [IsProper D.hom] [SmoothOfRelativeDimension 1 D.hom]
      [GeometricallyIntegral D.hom],
    (∃ i : SpecOver (R := Qbar) (Cover (f.map (algebraMap ℚ Qbar))) ⟶ D, IsOpenImmersion i.left) →
    ∀ (b : base Qbar ⟶ D) (A : GroupScheme Qbar) (e : A ≅ groupScheme Qbar D.hom)
      (m : D ⟶ A.X) (P : Pointed b e m) (v : IgusaCoordinates) (w : ℚ),
      w ≠ 0 → IgusaCoordinates.ofSextic f = v.scale w →
      moduliClass (polarizedLabel A P.determinantLine) = read v

theorem signed_class_of_igusa {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    moduliClass (polarizedLabel (geometricJacobian hu) (signedThetaLine hu)) =
      read (bgCoordinates (SixContact.J u)) := by
  let D := paperCurve u
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  let : Smooth (paperModel ℚ u).hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 (paperModel ℚ u).hom :=
    SixJacobian.relative_dimension_one _ (paper_dimension ℚ u)
  let : IsProper D.hom := inferInstanceAs (IsProper (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : GeometricallyIntegral D.hom :=
    inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : SmoothOfRelativeDimension 1 D.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  have openChart : ∃ i : SpecOver (R := Qbar) (Cover ((paper ℚ u false).map (algebraMap ℚ Qbar))) ⟶ D,
      IsOpenImmersion i.left := by
    rw [paper_baseChange]
    exact ⟨baseChangedFiniteChart Qbar u,inferInstance⟩
  obtain ⟨w,hw,coords⟩ := signed_coordinates hu
  exact classification (paper ℚ u false) (OddModel.paper_degree hu) (paper_chart_regular ℚ hu false).2 D
    openChart (basepoint hu) (geometricJacobian hu) _ _ (signedPointed hu) _ w hw coords

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.polarizedClass_eq
#print axioms ZInQBlueprint.ShimuraAtlas.signed_coordinates
#print axioms ZInQBlueprint.ShimuraAtlas.signed_class_of_igusa
