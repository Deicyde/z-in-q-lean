import ThetaPullbackRigidity
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SectionVanishingClosedSubscheme

/-! The uniqueness of a divisor tested on points and on arbitrary schemes. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.ThetaLinearSystem
noncomputable section
universe u
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The zero section vanishes on the test morphism exactly when the pulled-back
ideal is zero. This works on nonreduced test schemes as well. -/
theorem vanishes_iff_comap_eq_bot {T : Scheme.{u}} (f : T ⟶ X) {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) :
    Scheme.Modules.pullbackSection f s = 0 ↔ (Scheme.Modules.zeroSchemeIdeal s).comap f = ⊥ := by
  rw [hL.comap_zeroSchemeIdeal f s, (hL.pullback f).zeroSchemeIdeal_eq_bot_iff]

/-- Comparing the two induced sections on every test scheme detects the complete
zero subscheme, also for nonreduced and positive-dimensional tests. -/
theorem vanishes_comp_iff (c : X ⟶ Spec (.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 c L = 1) (a t : Y ≅ X)
    (e : (Scheme.Modules.pullback a.hom).obj L ≅ (Scheme.Modules.pullback t.hom).obj L)
    {T : Scheme.{u}} (p : T ⟶ Y) :
    Scheme.Modules.pullbackSection (p ≫ a.hom) s = 0 ↔
      Scheme.Modules.pullbackSection (p ≫ t.hom) s = 0 := by
  rw [vanishes_iff_comap_eq_bot _ hL, vanishes_iff_comap_eq_bot _ hL,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    comap_eq_of_pullback_linearly_equivalent c L hL s hs h0 a t e]

/-- Membership at an actual underlying scheme point. -/
theorem point_mem_iff (c : X ⟶ Spec (.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 c L = 1) (a t : Y ≅ X)
    (e : (Scheme.Modules.pullback a.hom).obj L ≅ (Scheme.Modules.pullback t.hom).obj L)
    (y : Y) :
    a.hom y ∈ (Scheme.Modules.zeroSchemeIdeal s).support ↔
      t.hom y ∈ (Scheme.Modules.zeroSchemeIdeal s).support := by
  have h := comap_eq_of_pullback_linearly_equivalent c L hL s hs h0 a t e
  change y ∈ ((Scheme.Modules.zeroSchemeIdeal s).support.preimage a.hom.continuous) ↔
    y ∈ ((Scheme.Modules.zeroSchemeIdeal s).support.preimage t.hom.continuous)
  rw [← Scheme.IdealSheafData.support_comap, ← Scheme.IdealSheafData.support_comap, h]

/-- Over a field, vanishing of a section at the point is equivalent to membership
of its image in the topological support. The residue field can extend the ground field. -/
theorem field_vanishes_iff_mem {F : Type u} [Field F] (p : Spec (.of F) ⟶ X)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) :
    Scheme.Modules.pullbackSection p s = 0 ↔
      p (IsLocalRing.closedPoint F) ∈ (Scheme.Modules.zeroSchemeIdeal s).support := by
  rw [vanishes_iff_comap_eq_bot p hL s, ← Scheme.IdealSheafData.support_eq_top_iff,
    Scheme.IdealSheafData.support_comap]
  constructor
  · intro h
    change IsLocalRing.closedPoint F ∈ (Scheme.Modules.zeroSchemeIdeal s).support.preimage p.continuous
    rw [h]
    trivial
  · intro h
    apply top_unique
    intro x _
    have he : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    subst x
    exact h

/-- The field-valued points defined by the reduced support. -/
def fieldSupport {A : Over (Spec (.of k))} (I : A.left.IdealSheafData) :
    Set (Over.mk (𝟙 (Spec (.of k))) ⟶ A) :=
  {p | p.left (IsLocalRing.closedPoint k) ∈ I.support}

/-- Images under two isomorphisms over the field, specified by pullback
along their inverses. The input can equivalently use a single
automorphism and one translation on an abelian variety. -/
theorem image_fieldSupport_eq {A B : Over (Spec (.of k))} (L : A.left.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ A.left.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 A.hom L = 1) (a t : A ≅ B)
    (e : (Scheme.Modules.pullback a.inv.left).obj L ≅ (Scheme.Modules.pullback t.inv.left).obj L) :
    (fun p => p ≫ a.hom) '' fieldSupport (A := A) (Scheme.Modules.zeroSchemeIdeal s) =
      (fun p => p ≫ t.hom) '' fieldSupport (A := A) (Scheme.Modules.zeroSchemeIdeal s) := by
  have he (p : Over.mk (𝟙 (Spec (.of k))) ⟶ B) :
      p ≫ a.inv ∈ fieldSupport (Scheme.Modules.zeroSchemeIdeal s) ↔
      p ≫ t.inv ∈ fieldSupport (Scheme.Modules.zeroSchemeIdeal s) :=
    point_mem_iff A.hom L hL s hs h0 ((Over.forget _).mapIso a.symm)
      ((Over.forget _).mapIso t.symm) e (p.left (IsLocalRing.closedPoint k))
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨(q ≫ a.hom) ≫ t.inv,(he _).mp ?_,by simp⟩
    simpa only [Category.assoc, a.hom_inv_id, Category.comp_id] using hq
  · rintro ⟨q,hq,rfl⟩
    refine ⟨(q ≫ t.hom) ≫ a.inv,(he _).mpr ?_,by simp⟩
    simpa only [Category.assoc, t.hom_inv_id, Category.comp_id] using hq

end
end ZInQBlueprint.ThetaLinearSystem
#print axioms ZInQBlueprint.ThetaLinearSystem.vanishes_iff_comap_eq_bot
#print axioms ZInQBlueprint.ThetaLinearSystem.vanishes_comp_iff
#print axioms ZInQBlueprint.ThetaLinearSystem.point_mem_iff
#print axioms ZInQBlueprint.ThetaLinearSystem.field_vanishes_iff_mem
#print axioms ZInQBlueprint.ThetaLinearSystem.image_fieldSupport_eq
