import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Closed subcurves over an algebraically closed field are recovered scheme-theoretically
from their geometric image provided their sources are reduced. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQBlueprint.ThetaSubcurve

noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
abbrev base (K : Type u) [Field K] := Spec (CommRingCat.of K)
abbrev point (K : Type u) [Field K] : Over (base K) := Over.mk (𝟙 _)

def pointImage {C A : Over (base K)} (i : C ⟶ A) : Set (point K ⟶ A) :=
  Set.range (fun p : point K ⟶ C => p ≫ i)

set_option backward.isDefEq.respectTransparency false in
/-- Containment on geometric points forces containment of the full underlying ranges.
Only the source of the first arrow needs to be locally of finite type. -/
theorem range_subset_of_points {C D A : Over (base K)} [LocallyOfFiniteType C.hom]
    (i : C ⟶ A) (j : D ⟶ A) [IsClosedImmersion j.left]
    (h : pointImage i ⊆ pointImage j) : Set.range i.left ⊆ Set.range j.left := by
  let : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  have hs : IsClosed (i.left ⁻¹' Set.range j.left) :=
    j.left.isClosedEmbedding.isClosed_range.preimage i.left.continuous
  have hcl : closedPoints C.left ⊆ i.left ⁻¹' Set.range j.left := by
    intro x hx
    let p : point K ⟶ C := Over.homMk (pointOfClosedPoint C.hom x hx)
      (pointOfClosedPoint_comp C.hom x hx)
    obtain ⟨q,hq⟩ := h ⟨p,rfl⟩
    refine ⟨q.left (IsLocalRing.closedPoint K), ?_⟩
    have he := congrArg (fun v : point K ⟶ A => v.left (IsLocalRing.closedPoint K)) hq
    change j.left (q.left (IsLocalRing.closedPoint K)) = i.left ((pointOfClosedPoint C.hom x hx) (IsLocalRing.closedPoint K)) at he
    rw [pointOfClosedPoint_apply] at he
    exact he
  have hall := closure_minimal hcl hs
  rw [closure_closedPoints] at hall
  rintro _ ⟨x,rfl⟩
  exact hall (Set.mem_univ x)

/-- A morphism from a reduced scheme factors through a closed immersion
once its underlying topological image lies there. -/
theorem lift_of_range {X Y A : Scheme.{u}} [IsReduced X]
    (f : X ⟶ A) (j : Y ⟶ A) [IsClosedImmersion j]
    (h : Set.range f ⊆ Set.range j) : ∃! l : X ⟶ Y, l ≫ j = f := by
  let : Surjective (pullback.fst f j) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_iff_forall.mpr fun x => h ⟨x,rfl⟩
  let : IsIso (pullback.fst f j) := isIso_of_isClosedImmersion_of_surjective _
  let l := inv (pullback.fst f j) ≫ pullback.snd f j
  have hl : l ≫ j = f := by simp [l, ← pullback.condition]
  exact ⟨l,hl,fun y hy => (cancel_mono j).mp (hy.trans hl.symm)⟩

/-- Factorization over the base, uniquely determined by geometric point containment. -/
theorem lift_of_pointImage {C D A : Over (base K)} [LocallyOfFiniteType C.hom]
    [IsReduced C.left] (i : C ⟶ A) (j : D ⟶ A) [IsClosedImmersion j.left]
    (h : pointImage i ⊆ pointImage j) : ∃! z : C ⟶ D, z ≫ j = i := by
  obtain ⟨l,hl,_⟩ := lift_of_range i.left j.left (range_subset_of_points i j h)
  let z : C ⟶ D := Over.homMk l (by rw [← j.w, ← Category.assoc, hl, i.w])
  have hz : z ≫ j = i := Over.OverMorphism.ext hl
  let : Mono j := Over.mono_of_mono_left _
  exact ⟨z,hz,fun y hy => (cancel_mono j).mp (hy.trans hz.symm)⟩

/-- An isomorphism of ambient schemes that takes one reduced closed subcurve's
geometric point image onto the other's restricts to a unique relative isomorphism. -/
theorem iso_of_pointImage {C D A B : Over (base K)}
    [IsReduced C.left] [IsReduced D.left] [LocallyOfFiniteType C.hom] [LocallyOfFiniteType D.hom]
    (i : C ⟶ A) (j : D ⟶ B) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : A ≅ B) (h : pointImage (i ≫ e.hom) = pointImage j) :
    ∃! z : C ≅ D, z.hom ≫ j = i ≫ e.hom := by
  let t := i ≫ e.hom
  let : IsClosedImmersion t.left := by
    change IsClosedImmersion (i.left ≫ e.hom.left)
    infer_instance
  let : Mono t := Over.mono_of_mono_left _
  let : Mono j := Over.mono_of_mono_left _
  obtain ⟨f,hf,_⟩ := lift_of_pointImage t j h.le
  obtain ⟨g,hg,_⟩ := lift_of_pointImage j t h.ge
  let z : C ≅ D := ⟨f,g,(cancel_mono t).mp (by simp [Category.assoc,hg,hf]),
    (cancel_mono j).mp (by simp [Category.assoc,hg,hf])⟩
  exact ⟨z,hf,fun y hy => Iso.ext ((cancel_mono j).mp (hy.trans hf.symm))⟩

end
end ZInQBlueprint.ThetaSubcurve

#print axioms ZInQBlueprint.ThetaSubcurve.range_subset_of_points
#print axioms ZInQBlueprint.ThetaSubcurve.lift_of_range
#print axioms ZInQBlueprint.ThetaSubcurve.lift_of_pointImage
#print axioms ZInQBlueprint.ThetaSubcurve.iso_of_pointImage
