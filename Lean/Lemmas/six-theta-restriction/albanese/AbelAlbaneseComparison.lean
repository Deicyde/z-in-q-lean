import SixThetaRestriction

/-! Comparing divisor presentations of a based curve with its Albanese factorization. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelComparison
open SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
  {hbase : i.hom ≫ C.hom = M.toBase} {V W : AbelianModel.GroupScheme K} {b : base K ⟶ C}

def onPoints (f : V ⟶ W) : Additive (base K ⟶ V.X) →+ Additive (base K ⟶ W.X) where
  toFun p := Additive.ofMul (p.toMul ≫ f.hom.hom.hom)
  map_zero' := by
    change (1 : base K ⟶ V.X) ≫ f.hom.hom.hom = 1
    exact MonObj.one_comp _
  map_add' p q := MonObj.mul_comp p.toMul q.toMul _

/-- An Albanese factor has the unique prescribed value on every degree-zero class. -/
theorem factor_on_points (A : AbelPresentation C M i hbase V b)
    (B : AbelPresentation C M i hbase W b) (f : V ⟶ W)
    (fac : A.morphism ≫ f.hom.hom.hom = B.morphism) :
    onPoints f = (A.divisorEquiv.symm.trans B.divisorEquiv).toAddMonoidHom := by
  apply AddMonoidHom.eq_of_eqOn_dense A.generate
  rintro _ ⟨⟨p,q⟩,rfl⟩
  have pt (v : base K ⟶ C) : onPoints f (A.abel v) = B.abel v := by
    change (v ≫ A.morphism) ≫ f.hom.hom.hom = v ≫ B.morphism
    rw [Category.assoc,fac]
  calc
    onPoints f (A.abel p - A.abel q) = B.abel p - B.abel q := by rw [map_sub,pt,pt]
    _ = (A.divisorEquiv.symm.trans B.divisorEquiv).toAddMonoidHom (A.abel p - A.abel q) := by
      rw [A.difference_class,B.difference_class]
      change B.divisorEquiv _ = B.divisorEquiv (A.divisorEquiv.symm (A.divisorEquiv _))
      rw [A.divisorEquiv.symm_apply_apply]

theorem factor_bijective (A : AbelPresentation C M i hbase V b)
    (B : AbelPresentation C M i hbase W b) (f : V ⟶ W)
    (fac : A.morphism ≫ f.hom.hom.hom = B.morphism) : Function.Bijective (onPoints f) := by
  rw [factor_on_points A B f fac]
  exact (A.divisorEquiv.symm.trans B.divisorEquiv).bijective

/-- Detection of isomorphisms is only required on the indicated two abelian varieties. -/
theorem closed_of_albanese (A : AbelPresentation C M i hbase V b)
    (B : AbelPresentation C M i hbase W b) (closed : IsClosedImmersion A.morphism.left)
    (factor : ∃ f : V ⟶ W, A.morphism ≫ f.hom.hom.hom = B.morphism)
    (detect : ∀ f : V ⟶ W, Function.Bijective (onPoints f) → IsIso f.hom.hom.hom.left) :
    IsClosedImmersion B.morphism.left := by
  obtain ⟨f,fac⟩ := factor
  let := closed
  let := detect f (factor_bijective A B f fac)
  rw [←fac]
  change IsClosedImmersion (A.morphism.left ≫ f.hom.hom.hom.left)
  infer_instance

open NormalDescent GeometricMarking GoodReductionJacobian SixThetaRestriction
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)
local notation "J" => geometricJacobian hu

/-- A classical closed pointed presentation with its Albanese factorization suffices
for the closed immersion of the chosen morphism on the actual sextic. -/
theorem signed_closed_of_albanese
    (data : letI := sourceIntegral hu
            letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
            let N := signedModel hu
            letI := N.curve
            ∃ (V : AbelianModel.GroupScheme Qbar)
                (A : AbelPresentation (paperCurve u) N.model N.iso N.hbase V (basepoint hu)),
              IsClosedImmersion A.morphism.left ∧
              (∃ f : V ⟶ J, A.morphism ≫ f.hom.hom.hom = (realization hu).morphism) ∧
              (∀ f : V ⟶ J, Function.Bijective (onPoints f) → IsIso f.hom.hom.hom.left)) :
    IsClosedImmersion (abelMorphism hu).left := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  obtain ⟨V,A,hc,hf,hd⟩ := data
  exact closed_of_albanese A (realization hu) hc hf hd
end
end ZInQBlueprint.SixAbelComparison
#print axioms ZInQBlueprint.SixAbelComparison.factor_on_points
#print axioms ZInQBlueprint.SixAbelComparison.factor_bijective
#print axioms ZInQBlueprint.SixAbelComparison.closed_of_albanese
#print axioms ZInQBlueprint.SixAbelComparison.signed_closed_of_albanese
