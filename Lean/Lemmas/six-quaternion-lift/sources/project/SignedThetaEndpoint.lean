import SignedCanonicalTheta
import CanonicalPolarization
import LabelledModuliField
import PoincareEndpoint
import ActualPeriodHeight

/-! The conditional bounded polynomial on the signed Jacobian. The chosen
line is the Poincaré determinant. Its nonzero section and its vanishing on
the normalized Abel curve are theorems for every off-contact fibre. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent CanonicalTheta
open JacobianHeight JacobianConductor LocalJacobians ZInQ
noncomputable section

/-- The three consequences of the classical canonical principal polarization.
Only the class of this particular theta line is required to be rational. -/
structure DeterminantPolarization {u : ℚ} (hu : u ∉ contactSet) : Prop where
  one : ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1
  principal : PrincipalTranslations (A:=geometricJacobian hu) (signedThetaLine hu)
  rational : RationalThetaClass (hu:=hu) (signedThetaLine hu)

/-- The published marked field of moduli at one compatible lift of the printed sextic. -/
def PrintedField {u : ℚ} (hu : u ∉ contactSet) : Prop :=
  ∃ (d : Qbar) (hd : d^2=6) (v : Qbar) (hv : v^2=PrintedModel.factor u d)
    (z : Qbar), z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar) ∧
    LabelledModuli (PrintedModel.jacobian hu hd)
      (printedBundle (PrintedModel.jacobianIso hu hd v hv) (signedThetaLine hu)) z

theorem marked_signed_jacobian {u : ℚ} (hu : u ∉ contactSet) (emb : SixAbelMap.PaperEmbedding hu)
    (coords : SixAbelMap.OpenCurveLifts hu) (theta : DeterminantPolarization hu) (field : PrintedField hu) :
    Nonempty (MarkedAction u (SixJacobian.jacobian hu)) := by
  obtain ⟨d,hd,v,hv,z,hz,moduli⟩ := field
  let e := PrintedModel.jacobianIso hu hd v hv
  let D := SixAbelMap.rigidDivisors hu
  have marked := classMarking_of_labelled_field e (signedThetaLine hu) theta.rational z hz moduli
  have family := printed_of_class D _ (signedThetaLine_invertible hu) _ (signedThetaSection_ne_zero hu)
    (fun p => Set.ext_iff.mp (signedThetaSection_zeros hu) p) theta.one theta.principal e marked
  exact marked_of_theta D e (SixThetaRestriction.polarizedTorelli_of_presentation hu D
    (SixAbelMap.rigidMorphism hu) (SixAbelMap.rigid_on_points hu)
    (SixAbelMap.rigid_closed_of_pointed hu emb) ((SixAbelMap.curve_lifts_iff_open hu).mpr coords)) family

/-- The determinant construction supplies the Abel curve and the Gaussian
bound supplies the analytic estimate for the actual theta series. -/
theorem original_of_signed_theta (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (embedding : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.PaperEmbedding hu)
    (coords : ∀ (u : ℚ) (hu : u ∉ contactSet), SixAbelMap.OpenCurveLifts hu)
    (theta : ∀ (u : ℚ) (hu : u ∉ contactSet), DeterminantPolarization hu)
    (bg : ∀ (u : ℚ) (hu : u ∉ contactSet), PrintedField hu)
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  PeriodGaussian.original_of_marking_and_periods hF effective
    (fun u hu => marked_signed_jacobian hu (embedding u hu) (coords u hu) (theta u hu) (bg u hu))
    (fun _ hu => good_outside ddmm hu) periods genus rank

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.DeterminantPolarization
#print axioms ZInQBlueprint.ThetaClass.PrintedField
#print axioms ZInQBlueprint.ThetaClass.marked_signed_jacobian
#print axioms ZInQBlueprint.ThetaClass.original_of_signed_theta
