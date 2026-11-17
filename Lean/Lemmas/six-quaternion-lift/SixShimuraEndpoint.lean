import SignedThetaEndpoint
import SixRationalCM
import SixShimuraChart
import SixPolarizedTransport

/-! The two uses of the Shimura curve are separated: its coarse real-labelled
moduli map is defined over Q, and its unmarked ppav is the Jacobian of the
printed sextic. All choices and isomorphisms after this comparison are
constructed in Lean. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.QuaternionLift
open ThetaClass QuaternionMarking NormalDescent AbelianModel GeometricMarking CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A polarized representative of the Shimura point before forgetting the
quaternionic embedding. No isomorphism to any Galois conjugate is required. -/
structure PolarizedRealization (U : ShimuraClassMap) (p : ConicPoint)
    (P : GroupScheme Qbar) (B : P.X.left.Modules) where
  surface : GroupScheme Qbar
  theta : surface.X.left.Modules
  order : LevelThree.O →+* End surface
  faithful : Function.Injective order
  represents : U.value p = moduliClass (markedObject surface theta order)
  comparison : surface ≅ P
  polarized : SameClass surface.X.hom theta (pullModule (underlying comparison).hom B)

theorem labelled_of_realization (U : ShimuraClassMap) (p : ConicPoint)
    {P : GroupScheme Qbar} {B : P.X.left.Modules} (m : PolarizedRealization U p P B) :
    LabelledModuli P B p.quotientCoordinate := by
  refine labelled_transport m.comparison m.polarized _ ?_
  apply (labelled_iff_fixed_class _ _ _).mpr
  refine ⟨m.order,m.faithful,?_⟩
  intro σ h
  simpa only [m.represents] using fixed_of_coordinate U p σ h

/-- The ordinary locus in the published rational CM table.  Projective
cross-multiplication includes the row at infinity. -/
def OutsideCM (j : ℚ) : Prop := ∀ a ∈ rationalCMRows,
  |(-27 * j / 16) * (a.2.2 : ℚ)| ≠ (a.2.1 : ℚ)

/-- The geometric consequence needed from Baba–Granath 3.14–3.15: on the
non-CM locus, an unmarked polarized comparison to a representative of one
point on the conic. Both radicals are existential and no field-of-moduli
input on the printed sextic is required. -/
def PrintedComparison (U : ShimuraClassMap) : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), OutsideCM (SixContact.J u) →
    ∃ (p : ConicPoint), FibrePoint u p ∧
    ∃ (d : Qbar) (hd : d^2 = 6) (v : Qbar) (hv : v^2 = PrintedModel.factor u d),
      Nonempty (PolarizedRealization U p (PrintedModel.jacobian hu hd)
        (printedBundle (PrintedModel.jacobianIso hu hd v hv) (signedThetaLine hu)))

/-- The actual header consumed by the six-contact proof. -/
theorem printedField_of_shimura (U : ShimuraClassMap) (models : PrintedComparison U)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrintedField hu := by
  obtain ⟨p,hp,d,hd,v,hv,⟨m⟩⟩ := models u hu (fun _ ha => avoids_cm_table hu ha)
  obtain ⟨_,square,_⟩ := marked_quotient_coordinate hu hp.y_square hp.z_square
  exact ⟨d,hd,v,hv,p.quotientCoordinate,square,labelled_of_realization U p m⟩

/-- A single compatible lift supplies the same labelled field statement on
every printed Jacobian for both d, both v and both signs of the field radical. -/
theorem all_printed_lifts {u : ℚ} (hu : u ∉ ZInQ.contactSet) (field : PrintedField hu)
    {d : Qbar} (hd : d^2 = 6) (v : Qbar) (hv : v^2 = PrintedModel.factor u d)
    {z : Qbar} (hz : z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar)) :
    LabelledModuli (PrintedModel.jacobian hu hd)
      (printedBundle (PrintedModel.jacobianIso hu hd v hv) (signedThetaLine hu)) z := by
  obtain ⟨d₀,hd₀,v₀,hv₀,z₀,hz₀,m⟩ := field
  let f := PrintedModel.jacobianIso hu hd₀ v₀ hv₀
  let g := PrintedModel.jacobianIso hu hd v hv
  exact (labelled_root_iff _ _ (hz₀.trans hz.symm)).mp
    (labelled_transport (f.symm ≪≫ g) (between_models f g (signedThetaLine hu)) _ m)

end
end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.labelled_of_realization
#print axioms ZInQBlueprint.QuaternionLift.printedField_of_shimura
#print axioms ZInQBlueprint.QuaternionLift.all_printed_lifts
