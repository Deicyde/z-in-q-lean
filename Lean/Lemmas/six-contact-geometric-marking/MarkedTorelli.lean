import PicardSigns
import GeometricPointDetection
import JacobianDiscriminant

/-! A comparison with the actual rational Picard scheme. The curve-specific
automorphism calculation is in PaperSexticSigns; the remaining inputs describe
geometric Picard points, Torelli, and the labelled field of moduli. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.GeometricMarking
open MarkedForm CurveChart AbelianModel NormalDescent JacobianHeight
open scoped NormalDescent
noncomputable section
set_option maxHeartbeats 2500000

abbrev geometricJacobian {u : ℚ} (hu : u∉ZInQ.contactSet) :=
  (Over.pullback (specExtension ℚ Qbar)).mapCommGrp.obj (SixJacobian.jacobian hu)

abbrev SchemeEnd {u : ℚ} (hu : u∉ZInQ.contactSet) :=
  (geometricJacobian hu).X.left ⟶ (geometricJacobian hu).X.left

abbrev Inversion {u : ℚ} (hu : u∉ZInQ.contactSet) : SchemeEnd hu :=
  (GrpObj.inv (X := (geometricJacobian hu).X)).left

abbrev δ (u : ℚ) : Qbar := (GlobalTwist.delta u : Qbar)

abbrev FibrePoints (u : ℚ) := Points (paperForm u (δ u))

/-- Coordinate point and divisor-class identification on the base change of the
actual unpointed Picard variety. Relative endomorphisms are tested on genuine
scheme-valued Qbar-points. -/
abbrev PicardComparison {u : ℚ} (hu : u∉ZInQ.contactSet) (G : Type*) [AddCommGroup G] :=
  MarkedPicard.Comparison (geometricJacobian hu).X.hom (Inversion hu) (FibrePoints u)
    (negY (paperForm u (δ u))) G

/-- Strong Torelli and the coordinate description of genus-two curve maps,
expressed on divisor classes. The conclusion gives coefficients via Lift,
and retains the abelian-scheme map before choosing coordinates. -/
def TorelliOnDifferences {u : ℚ} {hu : u∉ZInQ.contactSet} {G : Type*} [AddCommGroup G]
    (D : PicardComparison hu G) (polarized : SchemeEnd hu → Prop) : Prop :=
  ∀ a, polarized a → ∃ f : G →+ G, D.represents a f ∧ ∃ t : Lift u (δ u),
    ∀ p q, f (D.abel p-D.abel q)=D.abel (t.action p)-D.abel (t.action q)

/-- Every polarized automorphism supplied by Torelli on this specific rational
fibre is either identity or group inverse, without any separate Mestre test. -/
theorem polarized_signs {u : ℚ} {hu : u∉ZInQ.contactSet} {G : Type*} [AddCommGroup G]
    (D : PicardComparison hu G) {polarized : SchemeEnd hu → Prop}
    (T : TorelliOnDifferences D polarized) (a : SchemeEnd hu) (ha : polarized a) :
    a=𝟙 _ ∨ a=Inversion hu := by
  obtain ⟨f,hf,t,ht⟩ := T a ha
  have hd : δ u≠0 := by
    exact_mod_cast (Nat.ne_of_gt (GlobalTwist.delta_pos u))
  let : Smooth (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).smooth
  let : IsProper (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).proper
  let : Smooth (geometricJacobian hu).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let : IsProper (geometricJacobian hu).X.hom :=
    inferInstanceAs (IsProper (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let : IsReduced (geometricJacobian hu).X.left :=
    isReduced_of_smooth_over_field (g := (geometricJacobian hu).X.hom) inferInstance
  rcases picard_action_sign hu hd D.abel D.generate D.fibres f t ht with h|h
  · exact Or.inl (D.faithful hf (h.symm ▸ D.represents_id))
  · exact Or.inr (D.faithful hf (h.symm ▸ D.represents_inv (Over.w (GrpObj.inv (X := (geometricJacobian hu).X)))))

/-- The marked field of moduli gives corrections commuting with the specified
generator, not merely a setwise Galois-stable subring. -/
def Labelled {u : ℚ} {hu : u∉ZInQ.contactSet}
    (embedding : realOrder →+* End (geometricJacobian hu))
    (polarized : SchemeEnd hu → Prop) : Prop :=
  IsSquare (-(27*SixContact.J u+16)/SixContact.J u) →
    let E := (embedding QuadraticAlgebra.omega).asHom.hom.hom.hom.left
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ a, polarized a ∧
      (deck (SixJacobian.jacobian hu).X.hom σ ≫ a) ≫ E =
        E ≫ deck (SixJacobian.jacobian hu).X.hom σ ≫ a

/-- Constructor for the previously frozen MarkedAction on the literal
six-contact Jacobian. -/
def markedAction {u : ℚ} {hu : u∉ZInQ.contactSet} {G : Type*} [AddCommGroup G]
    (D : PicardComparison hu G) (polarized : SchemeEnd hu → Prop)
    (T : TorelliOnDifferences D polarized)
    (embedding : realOrder →+* End (geometricJacobian hu)) (injective : Function.Injective embedding)
    (labelled : Labelled embedding polarized) : MarkedAction u (SixJacobian.jacobian hu) where
  embedding := embedding
  faithful := injective
  polarized := polarized
  labelled := labelled
  signs := fun _ a ha => polarized_signs D T a ha

theorem rationalRM {u : ℚ} {hu : u∉ZInQ.contactSet} {G : Type*} [AddCommGroup G]
    (D : PicardComparison hu G) (polarized : SchemeEnd hu → Prop)
    (T : TorelliOnDifferences D polarized)
    (embedding : realOrder →+* End (geometricJacobian hu)) (injective : Function.Injective embedding)
    (labelled : Labelled embedding polarized) : RationalRM (SixJacobian.jacobian hu) :=
  rationalRM_of_marked (markedAction D polarized T embedding injective labelled)

end
end ZInQBlueprint.GeometricMarking
#print axioms ZInQBlueprint.GeometricMarking.polarized_signs
#print axioms ZInQBlueprint.GeometricMarking.markedAction
#print axioms ZInQBlueprint.GeometricMarking.rationalRM
