import CurveMarkedDescent

/-! Removing both the translation and the choice of sign from the action on a
pointed Abel map. The degree-two pencil supplies the second sign. -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent

namespace ZInQBlueprint.AbelComparison
open AbelianModel NormalDescent QuaternionMarking ThetaClass CMRepair GeometricMarking SixAbelMap WeightedCurvePoints

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Value of a geometric morphism at a geometric point, in additive notation. -/
abbrev abelValue {C : Over (Spec (.of Qbar))} {A : GroupScheme Qbar}
    (m : C ⟶ A.X) (p : base Qbar ⟶ C) : sections A :=
  Additive.ofMul (p ≫ m)

/-- The two signs and the translation in the pointed form of strong Torelli. -/
def AbelComparisonUpToSign {C : Over (Spec (.of Qbar))} {A : GroupScheme Qbar}
    (m : C ⟶ A.X) (a : A ≅ A) : Prop :=
  ∃ (c : C ≅ C) (t : sections A),
    (∀ p, abelValue (m ≫ (underlying a).hom) p = abelValue m (p ≫ c.hom) + t) ∨
    (∀ p, abelValue (m ≫ (underlying a).hom) p = -abelValue m (p ≫ c.hom) + t)

/-- If the Abel images of the two points in a fibre have constant sum,
composing with the deck involution absorbs the negative Torelli sign. -/
theorem differences_of_either_sign {C : Over (Spec (.of Qbar))} {A : GroupScheme Qbar}
    (m : C ⟶ A.X) (a : A ≅ A) (deck : C ≅ C)
    (fibres : ∀ p q : base Qbar ⟶ C,
      abelValue m p + abelValue m (p ≫ deck.hom) =
      abelValue m q + abelValue m (q ≫ deck.hom))
    (h : AbelComparisonUpToSign m a) : OnAbelDifferences m a := by
  obtain ⟨c,t,positive | negative⟩ := h
  · refine differences_of_abel_translate m a c t (fun p => ?_)
    simpa only [abelValue, Category.assoc] using positive p
  · refine ⟨c ≪≫ deck, fun p q => ?_⟩
    have act (v : base Qbar ⟶ C) :
        (Additive.ofMul ((v ≫ m) ≫ (underlying a).hom) : sections A) =
        -abelValue m (v ≫ c.hom) + t := by
      simpa only [abelValue, Category.assoc] using negative v
    rw [act, act]
    calc
      _ = abelValue m (q ≫ c.hom) - abelValue m (p ≫ c.hom) := by abel
      _ = abelValue m ((p ≫ c.hom) ≫ deck.hom) - abelValue m ((q ≫ c.hom) ≫ deck.hom) :=
        sub_eq_sub_iff_add_eq_add.mpr ((fibres (p ≫ c.hom) (q ≫ c.hom)).symm.trans (add_comm _ _))
      _ = _ := by simp only [abelValue, Iso.trans_hom, Category.assoc]

/-- The divisor classes of the fibres of the explicit signed genus-two curve. -/
theorem signed_deck_sums {u : ℚ} (hu : u ∉ ZInQ.contactSet) (p q : base Qbar ⟶ paperCurve u) :
    abelValue (rigidMorphism hu) p + abelValue (rigidMorphism hu) (p ≫ (geometricDeck hu).hom) =
    abelValue (rigidMorphism hu) q + abelValue (rigidMorphism hu) (q ≫ (geometricDeck hu).hom) := by
  obtain ⟨x,rfl⟩ := (weightedEquiv_pullback hu).surjective p
  obtain ⟨y,rfl⟩ := (weightedEquiv_pullback hu).surjective q
  simpa only [rigid_on_points, weighted_deck, abelValue] using (rigidDivisors hu).fibres x y

theorem signed_differences {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (a : geometricJacobian hu ≅ geometricJacobian hu) (h : AbelComparisonUpToSign (rigidMorphism hu) a) :
    OnAbelDifferences (rigidMorphism hu) a :=
  differences_of_either_sign _ a (geometricDeck hu) (signed_deck_sums hu) h

end
end ZInQBlueprint.AbelComparison

#print axioms ZInQBlueprint.AbelComparison.differences_of_either_sign
#print axioms ZInQBlueprint.AbelComparison.signed_deck_sums
#print axioms ZInQBlueprint.AbelComparison.signed_differences
