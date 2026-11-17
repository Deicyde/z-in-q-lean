import PrintedPolarization

/-! The labelled field of moduli in Baba–Granath, pp. 738 and 747.
The conjugate line bundle is pulled back by the first projection from the
conjugate scheme. Rationality of a polarization is expressed in the
Néron–Severi group, allowing the Abel base point to move under Galois. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {u : ℚ} {hu : u ∉ ZInQ.contactSet} {P : GroupScheme Qbar}
local notation "J" => geometricJacobian hu

abbrev printedBundle (e : J ≅ P) (L : (geometricJacobian hu).X.left.Modules) :=
  pullModule (underlying e).inv L

abbrev projection (P : GroupScheme Qbar) (σ : Qbar ≃ₐ[ℚ] Qbar) :=
  pullback.fst P.X.hom (Spec.map (CommRingCat.ofHom σ.toRingHom))

/-- The group Galois action on the class of a specified line bundle. -/
def RationalThetaClass (L : (geometricJacobian hu).X.left.Modules) : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, SameClass (geometricJacobian hu).X.hom L
    ((Scheme.Modules.pullback (deck (SixJacobian.jacobian hu).X.hom σ)).obj L)

/-- For a rational modular parameter, fixing a generator z of its quadratic
extension suffices to preserve the marked polarized surface. -/
def LabelledModuli (P : GroupScheme Qbar) (B : P.X.left.Modules) (z : Qbar) : Prop :=
  ∃ act : LevelThree.O →+* End P, Function.Injective act ∧
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ z = z → ∃ φ : P ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj P,
      (act sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map
        (act sqrtThree).asHom ∧
      SameClass P.X.hom B (pullModule (underlying φ).hom ((Scheme.Modules.pullback (projection P σ)).obj B))

theorem fixes_sqrt_of_rational_square {x : ℚ} {z : Qbar} (hz : z^2 = (x : Qbar))
    (hx : IsSquare x) (σ : Qbar ≃ₐ[ℚ] Qbar) : σ z = z := by
  obtain ⟨r,hr⟩ := hx
  have hsq : z^2 = (r : Qbar)^2 := by rw [hz,hr]; push_cast; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h|h <;> rw [h] <;> simp

private def compPull {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj L := (Scheme.Modules.pullbackComp f g).app L

theorem printed_rational_projection (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (underlying (e ≪≫ rationalOnPrinted e σ)).hom.left ≫ projection P σ ≫ (underlying e).inv.left =
      deck (SixJacobian.jacobian hu).X.hom σ := by
  let c := rationalGroupComparison (SixJacobian.jacobian hu) σ
  have cancel : e.hom ≫ (rationalOnPrinted e σ).hom =
      c.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map e.hom := by simp [c,rationalOnPrinted]
  change (e.hom ≫ (rationalOnPrinted e σ).hom).hom.hom.hom.left ≫ _ = _
  rw [cancel]
  change (c.hom.hom.hom.hom.left ≫ _) ≫ _ ≫ _ = _
  rw [Category.assoc,←Category.assoc _ (projection P σ),pull_fst σ e.hom]
  have ident : e.hom.hom.hom.hom.left ≫ e.inv.hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun m : J ⟶ J => m.hom.hom.hom.left) e.hom_inv_id
  change c.hom.hom.hom.hom.left ≫ (pullback.fst _ _ ≫ e.hom.hom.hom.hom.left) ≫ e.inv.hom.hom.hom.left = _
  rw [Category.assoc _ e.hom.hom.hom.hom.left,ident,Category.comp_id]
  exact comparison_fst (SixJacobian.jacobian hu) σ

theorem classMarking_of_labelled_field (e : J ≅ P) (L : (geometricJacobian hu).X.left.Modules)
    (rat : RationalThetaClass (hu:=hu) L) (z : Qbar)
    (hz : z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar))
    (moduli : LabelledModuli P (printedBundle e L) z) : PrintedClassMarking e L := by
  obtain ⟨act,faithful,marked⟩ := moduli
  refine ⟨act,faithful,?_⟩
  intro square σ
  obtain ⟨φ,gen,polar⟩ := marked σ (fixes_sqrt_of_rational_square hz square σ)
  refine ⟨φ,gen,?_⟩
  let f := underlying (e ≪≫ φ)
  let g := underlying (e ≪≫ rationalOnPrinted e σ)
  let B := printedBundle e L
  let M := (Scheme.Modules.pullback (projection P σ)).obj B
  have h := polar.pull (underlying e).hom.left (underlying e).hom.w
  have hf : SameClass (geometricJacobian hu).X.hom L (pullModule f.hom M) :=
    (sameClass_transport (underlying e) L).trans
      (h.congr (Iso.refl _) (compPull (underlying e).hom.left (underlying φ).hom.left M))
  let back : pullModule g.hom M ≅ (Scheme.Modules.pullback (deck (SixJacobian.jacobian hu).X.hom σ)).obj L :=
    (Scheme.Modules.pullback g.hom.left).mapIso (compPull (projection P σ) (underlying e).inv.left L) ≪≫
      compPull g.hom.left _ L ≪≫ (Scheme.Modules.pullbackCongr (printed_rational_projection e σ)).app L
  have hg := (rat σ).congr (Iso.refl _) back.symm
  exact (sameClass_pull_comparison f g L M hf hg).congr (Iso.refl _)
    (compPull f.hom.left g.inv.left L).symm

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.fixes_sqrt_of_rational_square
#print axioms ZInQBlueprint.ThetaClass.printed_rational_projection
#print axioms ZInQBlueprint.ThetaClass.classMarking_of_labelled_field
