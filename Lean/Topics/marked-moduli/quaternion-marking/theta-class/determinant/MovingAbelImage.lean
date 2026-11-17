import SignedCartier
import SignedRigidGalois

/-! Turning the Galois action on point differences into descent of the
canonical class. The translation is shared by the whole Abel curve. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent CanonicalTheta SixAbelMap AbelGalois
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

def signedGalois (σ : Qbar ≃ₐ[ℚ] Qbar) : JacobianPoints hu ≃+ JacobianPoints hu where
  toEquiv := (Additive.ofMul : _ ≃ _).symm.trans
    ((galoisEquiv (SixJacobian.jacobian hu).X σ).trans Additive.ofMul)
  map_add' p q := by
    let A := SixJacobian.jacobian hu
    let e := pointAddEquiv (L:=Qbar) A
    let c : Additive (fieldTest ℚ Qbar ⟶ A.X) →+ Additive (fieldTest ℚ Qbar ⟶ A.X) :=
      { toFun z := Additive.ofMul (coefficient σ ≫ z.toMul)
        map_zero' := by
          change Additive.ofMul (coefficient σ ≫ (1 : fieldTest ℚ Qbar ⟶ A.X)) =
            Additive.ofMul (1 : fieldTest ℚ Qbar ⟶ A.X)
          exact congrArg Additive.ofMul (MonObj.comp_one _)
        map_add' p q := congrArg Additive.ofMul (MonObj.comp_mul (coefficient σ) p.toMul q.toMul) }
    change e (c (e.symm (p+q))) = e (c (e.symm p)) + e (c (e.symm q))
    rw [map_add,map_add,map_add]

def curveGalois (σ : Qbar ≃ₐ[ℚ] Qbar) : Equiv.Perm (FibrePoints u) :=
  (WeightedCurvePoints.weightedEquiv_pullback hu).trans
    ((galoisEquiv (BinaryCover.paperModel ℚ u) σ).trans (WeightedCurvePoints.weightedEquiv_pullback hu).symm)

theorem image_of_differences {P G : Type*} [Nonempty P] [AddCommGroup G]
    (a : P → G) (g : G ≃+ G) (f : Equiv.Perm P)
    (naturality : ∀ p q, g (a p - a q) = a (f p) - a (f q)) :
    ∃ t, ∀ x, g.symm x ∈ Set.range a ↔ x+t ∈ Set.range a := by
  let b := Classical.choice (inferInstance : Nonempty P)
  let t := a (f b) - g (a b)
  have single (p : P) : g (a p) + t = a (f p) := by
    have eq := naturality p b
    rw [map_sub] at eq
    dsimp [t]
    calc
      _ = (g (a p) - g (a b)) + a (f b) := by abel
      _ = _ := by rw [eq,sub_add_cancel]
  refine ⟨t,fun x => ⟨?_,?_⟩⟩
  · rintro ⟨p,hp⟩
    have hx : g (a p)=x := (congrArg g hp).trans (g.apply_symm_apply x)
    exact ⟨f p,(single p).symm.trans (congrArg (· + t) hx)⟩
  · rintro ⟨p,hp⟩
    refine ⟨f.symm p,g.injective ?_⟩
    rw [g.apply_symm_apply]
    apply (add_left_inj t).mp
    exact (single (f.symm p)).trans ((congrArg a (f.apply_symm_apply p)).trans hp)

/-- On a field spectrum precomposition with an automorphism preserves the
test for vanishing. The inverse in this formula fixes the sign convention. -/
theorem deck_vanishes (σ : Qbar ≃ₐ[ℚ] Qbar) (x : JacobianPoints hu) :
    Scheme.Modules.pullbackSection (x.toMul.left ≫ deck (SixJacobian.jacobian hu).X.hom σ)
      (signedThetaSection hu) = 0 ↔ (signedGalois hu σ).symm x ∈ Set.range (rigidDivisors hu).abel := by
  let p := ((signedGalois hu σ).symm x).toMul
  have h := galoisPoint_deck (X := (SixJacobian.jacobian hu).X) σ p
  have cancel : galoisPoint σ p = x.toMul :=
    congrArg Additive.toMul ((signedGalois hu σ).apply_symm_apply x)
  rw [cancel] at h
  rw [h,ThetaLinearSystem.field_vanishes_iff_mem _ (signedThetaLine_invertible hu)]
  have point : (Spec.map (CommRingCat.ofHom σ.toRingHom)) (IsLocalRing.closedPoint Qbar) =
      IsLocalRing.closedPoint Qbar := Subsingleton.elim _ _
  change p.left ((Spec.map (CommRingCat.ofHom σ.toRingHom)) _) ∈ _ ↔ _
  rw [point]
  exact (ThetaLinearSystem.field_vanishes_iff_mem p.left (signedThetaLine_invertible hu)
    (signedThetaSection hu)).symm.trans (Set.ext_iff.mp (signedThetaSection_zeros hu) _)

def AbelDifferenceNaturality : Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (p q : FibrePoints u),
    signedGalois hu σ ((rigidDivisors hu).abel p - (rigidDivisors hu).abel q) =
      (rigidDivisors hu).abel (curveGalois hu σ p) - (rigidDivisors hu).abel (curveGalois hu σ q)

/-- Both descriptions use the same normalized base point. The right side
is the class represented by the difference of the two relative graphs. -/
def RigidPointClass : Prop :=
  ∀ p : CurvePoints u, Additive.ofMul (p ≫ rigidMorphism hu) =
    signedDifference hu p (basepoint hu)

theorem difference_of_rigid_point_class (ident : RigidPointClass hu) : AbelDifferenceNaturality hu := by
  let c := WeightedCurvePoints.weightedEquiv_pullback hu
  let b := basepoint hu
  have eq (p q : FibrePoints u) :
      (rigidDivisors hu).abel p - (rigidDivisors hu).abel q = signedDifference hu (c p) (c q) := by
    rw [rigid_on_points,rigid_on_points,ident,ident]
    exact sub_eq_iff_eq_add.mpr (signed_chain hu (c p) (c q) b).symm
  intro σ p q
  rw [eq,eq]
  have act (v : FibrePoints u) : c (curveGalois hu σ v) =
      galoisPoint (X:=BinaryCover.paperModel ℚ u) σ (c v) :=
    c.apply_symm_apply _
  rw [act,act]
  exact signed_galois hu σ (c p) (c q)

theorem deck_support_of_difference (natural : AbelDifferenceNaturality hu) : DeckAbelSupport hu := by
  let : Nonempty (FibrePoints u) := ⟨(WeightedCurvePoints.weightedEquiv_pullback hu).symm (basepoint hu)⟩
  intro σ
  obtain ⟨t,ht⟩ := image_of_differences (rigidDivisors hu).abel (signedGalois hu σ)
    (curveGalois hu σ) (natural σ)
  exact ⟨t,fun x => (deck_vanishes hu σ x).trans (ht x)⟩

theorem signed_deck_abel_support : DeckAbelSupport hu :=
  deck_support_of_difference hu (difference_of_rigid_point_class hu (rigid_point_class hu))

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.image_of_differences
#print axioms ZInQBlueprint.ThetaClass.deck_vanishes
#print axioms ZInQBlueprint.ThetaClass.difference_of_rigid_point_class
#print axioms ZInQBlueprint.ThetaClass.deck_support_of_difference
#print axioms ZInQBlueprint.ThetaClass.signed_deck_abel_support
