import SixAbelDivisorMap

/-! Geometric points generate the represented Jacobian by Abel differences. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj
open JacobianVarieties.Picard.Proofs.PicardPointsTransport.PtsIntertwineIso
namespace ZInQBlueprint.SixAbelMap
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
  {hbase : i.hom ≫ C.hom=M.toBase} {V : AbelianModel.GroupScheme K} {b : base K ⟶ C}

def AbelPresentation.abel (A : AbelPresentation C M i hbase V b) (p : base K ⟶ C) :
    Additive (base K ⟶ V.X) := Additive.ofMul (p ≫ A.morphism)

theorem difference_self (q : Place K F) : difference q q = 0 := Subtype.ext (sub_self _)
theorem difference_sub (p q b : Place K F) : difference p b - difference q b = difference p q := by
  apply Subtype.ext
  change (_ - _ : Divisor K F) - (_ - _) = _ - _
  abel

theorem AbelPresentation.abel_basepoint (A : AbelPresentation C M i hbase V b) : A.abel b = 0 := by
  rw [←show A.divisorEquiv (Pic0.mk (difference (pointPlace C M i hbase b) (pointPlace C M i hbase b))) = A.abel b from A.point_class b,
    difference_self]
  exact A.divisorEquiv.map_zero

theorem AbelPresentation.difference_class (A : AbelPresentation C M i hbase V b) (p q : base K ⟶ C) :
    A.abel p - A.abel q = A.divisorEquiv (Pic0.mk (difference (pointPlace C M i hbase p) (pointPlace C M i hbase q))) := by
  change Additive.ofMul (p ≫ A.morphism) - Additive.ofMul (q ≫ A.morphism) = _
  rw [←A.point_class,←A.point_class,←map_sub]
  apply congrArg A.divisorEquiv
  exact congrArg Pic0.mk (difference_sub _ _ _)

theorem AbelPresentation.generate (A : AbelPresentation C M i hbase V b) :
    AddSubgroup.closure (Set.range (fun r : (base K ⟶ C) × (base K ⟶ C) =>
      A.abel r.1-A.abel r.2)) = ⊤ := by
  let H := AddSubgroup.closure (Set.range (fun r : (base K ⟶ C) × (base K ⟶ C) =>
      A.abel r.1-A.abel r.2))
  let q := pointPlace C M i hbase b
  have member (P : Place K F) : Pic0.mk (difference P q) ∈ H.comap A.divisorEquiv.toAddMonoidHom := by
    obtain ⟨p,rfl⟩ := (pointPlace C M i hbase).surjective P
    change A.divisorEquiv (Pic0.mk _) ∈ H
    rw [←A.difference_class p b]
    exact AddSubgroup.subset_closure ⟨(p,b),rfl⟩
  have full : ⊤ ≤ H.comap A.divisorEquiv.toAddMonoidHom := by
    rw [←closure_range_mk_gen_eq_top (fun v : Place K F => IsCurveOver.deg_eq_one_of_isAlgClosed v) q]
    exact (AddSubgroup.closure_le _).mpr (Set.range_subset_iff.mpr member)
  apply top_unique
  intro y _
  obtain ⟨x,rfl⟩ := A.divisorEquiv.surjective y
  exact full (show x ∈ (⊤ : AddSubgroup (Pic0 K F)) from trivial)

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.abel_basepoint
#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.difference_class
#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.generate

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.SixAbelMap
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
  {hbase : i.hom ≫ C.hom=M.toBase} {V W : AbelianModel.GroupScheme K} {b : base K ⟶ C}

/-- Change the target by an isomorphism of group schemes, preserving every individual class. -/
def AbelPresentation.transport (A : AbelPresentation C M i hbase V b) (e : V ≅ W) :
    AbelPresentation C M i hbase W b where
  morphism := A.morphism ≫ e.hom.hom.hom.hom
  divisorEquiv := A.divisorEquiv.trans (pointsIso e)
  point_class p := (congrArg (pointsIso e) (A.point_class p)).trans
    (show (p ≫ A.morphism) ≫ e.hom.hom.hom.hom = p ≫ A.morphism ≫ e.hom.hom.hom.hom from Category.assoc _ _ _)
end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.transport
