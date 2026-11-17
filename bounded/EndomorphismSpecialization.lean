import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.Idempotents

/-!
# Specialization of product endomorphisms and an idempotent factor

The categorical arguments apply to objects considered up to isogeny. Their
hypotheses specify what must be verified about the geometric specialization
functor. The rational algebra statements allow the descent action to permute
the factors and to conjugate their endomorphisms.
-/

namespace ZOverQ.Qualitative.Specialization

open CategoryTheory CategoryTheory.Limits

/-- Full faithfulness on the endomorphisms of one object extends to the Hom
spaces between any two objects isomorphic to it. -/
theorem hom_bijective_of_reference {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {Z X Y : C} (x : X ≅ Z) (y : Y ≅ Z)
    (atReference : Function.Bijective (fun a : Z ⟶ Z => F.map a)) :
    Function.Bijective (fun a : X ⟶ Y => F.map a) := by
  let u := x.homCongr y
  let v := (F.mapIso x).homCongr (F.mapIso y)
  have compat (a : X ⟶ Y) : F.map (u a) = v (F.map a) := F.map_homCongr x y a
  constructor
  · intro a b h
    apply u.injective
    apply atReference.1
    exact (compat a).trans ((congrArg v h).trans (compat b).symm)
  · intro b
    obtain ⟨a, ha⟩ := atReference.2 (v b)
    refine ⟨u.symm a, v.injective ?_⟩
    calc v (F.map (u.symm a)) = F.map (u (u.symm a)) := (compat _).symm
      _ = F.map a := by rw [u.apply_symm_apply]
      _ = v b := ha

/-- A functor preserving the given finite biproduct induces a bijection on
its endomorphisms if it does so on a single reference factor. -/
theorem biproduct_end_bijective_of_reference {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasFiniteBiproducts C]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {I : Type} [Finite I]
    (X : I → C) [PreservesBiproduct X F] {Z : C} (iso : ∀ i, X i ≅ Z)
    (atReference : Function.Bijective (fun a : Z ⟶ Z => F.map a)) :
    Function.Bijective (fun a : ⨁ X ⟶ ⨁ X => F.map a) := by
  have entry (i j) := hom_bijective_of_reference F (iso i) (iso j) atReference
  constructor
  · intro a b h
    apply (biproduct.matrixEquiv (f := X) (g := X)).injective
    funext i j
    apply (entry i j).1
    change F.map (biproduct.ι X i ≫ a ≫ biproduct.π X j) =
      F.map (biproduct.ι X i ≫ b ≫ biproduct.π X j)
    simp only [F.map_comp, h]
  · intro b
    let entries i j := F.map (biproduct.ι X i) ≫ b ≫ F.map (biproduct.π X j)
    choose a ha using fun i j => (entry i j).2 (entries i j)
    refine ⟨biproduct.matrix a, ?_⟩
    let cone := isBilimitOfPreserves F (biproduct.isBilimit X)
    apply cone.isColimit.hom_ext
    intro i
    apply cone.isLimit.hom_ext
    intro j
    change (F.map (biproduct.ι X i.as) ≫ F.map (biproduct.matrix a)) ≫
      F.map (biproduct.π X j.as) = (F.map (biproduct.ι X i.as) ≫ b) ≫ F.map (biproduct.π X j.as)
    rw [Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp]
    change F.map (biproduct.components (biproduct.matrix a) i.as j.as) = entries i.as j.as
    rw [biproduct.matrix_components]
    exact ha i.as j.as

section Fixed

variable {G A B : Type*} [Group G] [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]

/-- Rational endomorphisms fixed by every element of the descent group. -/
def fixedAlgebra (act : G →* (A ≃ₐ[ℚ] A)) : Subalgebra ℚ A :=
  ⨅ g, (act g).toAlgHom.equalizer (AlgHom.id ℚ A)

theorem mem_fixedAlgebra (act : G →* (A ≃ₐ[ℚ] A)) (a : A) :
    a ∈ fixedAlgebra act ↔ ∀ g, act g a = a := by
  simp [fixedAlgebra]

/-- An equivariant algebra isomorphism restricts to the invariant subalgebras. -/
def onFixed (e : A ≃ₐ[ℚ] B) (s : G →* (A ≃ₐ[ℚ] A)) (t : G →* (B ≃ₐ[ℚ] B))
    (commutes : ∀ g a, e (s g a) = t g (e a)) :
    fixedAlgebra s ≃ₐ[ℚ] fixedAlgebra t where
  toFun a := ⟨e a, (mem_fixedAlgebra t _).2 fun g =>
    (commutes g a).symm.trans (congrArg e ((mem_fixedAlgebra s _).1 a.2 g))⟩
  invFun b := ⟨e.symm b, (mem_fixedAlgebra s _).2 fun g => e.injective (by
    rw [commutes, e.apply_symm_apply, (mem_fixedAlgebra t _).1 b.2 g])⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)
  map_mul' a b := Subtype.ext (e.map_mul a.val b.val)
  map_add' a b := Subtype.ext (e.map_add a.val b.val)
  commutes' r := Subtype.ext (e.commutes r)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Specialization on one endomorphism algebra extends entrywise to matrices
and descends to invariants. Equivariance is required only on whole matrices. -/
noncomputable def invariantSpecialization
    (ev : A →ₐ[ℚ] B) (rigidity : Function.Injective ev) (lifts : Function.Surjective ev)
    (s : G →* (Matrix I I A ≃ₐ[ℚ] Matrix I I A))
    (t : G →* (Matrix I I B ≃ₐ[ℚ] Matrix I I B))
    (equivariant : ∀ g M, ev.mapMatrix (s g M) = t g (ev.mapMatrix M)) :
    fixedAlgebra s ≃ₐ[ℚ] fixedAlgebra t :=
  onFixed (AlgEquiv.ofBijective ev ⟨rigidity, lifts⟩).mapMatrix s t equivariant

theorem invariantSpecialization_apply
    (ev : A →ₐ[ℚ] B) (rigidity : Function.Injective ev) (lifts : Function.Surjective ev)
    (s : G →* (Matrix I I A ≃ₐ[ℚ] Matrix I I A))
    (t : G →* (Matrix I I B ≃ₐ[ℚ] Matrix I I B))
    (equivariant : ∀ g M, ev.mapMatrix (s g M) = t g (ev.mapMatrix M))
    (M : fixedAlgebra s) (i j : I) :
    (invariantSpecialization ev rigidity lifts s t equivariant M).val i j = ev (M.val i j) :=
  rfl

end Fixed

section Corners

variable {A B : Type*} [Ring A] [Ring B]

theorem map_idempotent (e : A ≃+* B) {p : A} (hp : IsIdempotentElem p) :
    IsIdempotentElem (e p) := (e.map_mul p p).symm.trans (congrArg e hp.eq)

/-- A unital field action on the corner has rational scalars acting by scalar
multiples of the projector in the ambient endomorphism algebra. -/
theorem rational_scalar_in_corner [Algebra ℚ A] {K : Type*} [Field K] [Algebra ℚ K]
    {p : A} (hp : IsIdempotentElem p) (j : K →+* hp.Corner) (r : ℚ) :
    (j (algebraMap ℚ K r)).1 = algebraMap ℚ A r * p := by
  let incl : hp.Corner →+ A := ⟨⟨fun x => x.1, rfl⟩, fun _ _ => rfl⟩
  let f := incl.comp j.toAddMonoidHom
  have h1 : f 1 = p := congrArg (fun z : hp.Corner => z.1) j.map_one
  change f (algebraMap ℚ K r) = _
  simpa only [Algebra.smul_def, mul_one, h1] using map_rat_smul f r (1 : K)

/-- Transport of the actual corner rings. Their multiplicative identities are
the two projectors, which need not be central in the ambient rings. -/
def cornerEquiv (e : A ≃+* B) {p : A} (hp : IsIdempotentElem p) :
    hp.Corner ≃+* (map_idempotent e hp).Corner where
  toFun x := ⟨e x.1, by
    obtain ⟨a, ha⟩ := x.2
    exact ⟨e a, by simpa only [map_mul] using congrArg e ha⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨b, hb⟩ := y.2
    exact ⟨e.symm b, by simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hb⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (e.map_add x.1 y.1)
  map_mul' x y := Subtype.ext (e.map_mul x.1 y.1)

/-- Lift a fibre projector together with a unital field embedding into its
corner. Evaluation recovers each field element, and the lifted unit is the
lifted projector in the ambient algebra. Apply this to the ring equivalence
underlying `invariantSpecialization`. -/
theorem lift_projector_and_field (ev : A ≃+* B) {K : Type*} [Field K] {q : B}
    (hq : IsIdempotentElem q) (ι : K →+* hq.Corner) (faithful : Function.Injective ι) :
    ∃ (p : A) (hp : IsIdempotentElem p) (j : K →+* hp.Corner),
      ev p = q ∧ Function.Injective j ∧ (∀ a : K, ev (j a).1 = (ι a).1) ∧ (j 1).1 = p := by
  let e := cornerEquiv ev.symm hq
  let j := e.toRingHom.comp ι
  refine ⟨ev.symm q, map_idempotent ev.symm hq, j, ev.apply_symm_apply q,
    e.injective.comp faithful, ?_, ?_⟩
  · intro a
    exact ev.apply_symm_apply (ι a).1
  · exact congrArg (fun a : (map_idempotent ev.symm hq).Corner => a.1) j.map_one

end Corners

/-- The lifted field and projector lie in the invariant algebra, and their matrix
entries specialize by the original endomorphism homomorphism. -/
theorem lift_invariant_projector_and_field
    {A B G I K : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
    [Group G] [Fintype I] [DecidableEq I] [Field K]
    (ev : A →ₐ[ℚ] B) (rigidity : Function.Injective ev) (lifts : Function.Surjective ev)
    (s : G →* (Matrix I I A ≃ₐ[ℚ] Matrix I I A))
    (t : G →* (Matrix I I B ≃ₐ[ℚ] Matrix I I B))
    (equivariant : ∀ g M, ev.mapMatrix (s g M) = t g (ev.mapMatrix M))
    {q : fixedAlgebra t} (hq : IsIdempotentElem q) (ι : K →+* hq.Corner)
    (faithful : Function.Injective ι) :
    ∃ (p : fixedAlgebra s) (hp : IsIdempotentElem p) (j : K →+* hp.Corner),
      ev.mapMatrix p.val = q.val ∧ Function.Injective j ∧
      (∀ a : K, ev.mapMatrix (j a).1.val = (ι a).1.val) ∧ (j 1).1 = p := by
  let E := invariantSpecialization ev rigidity lifts s t equivariant
  obtain ⟨p, hp, j, he, hj, hfield, hunit⟩ :=
    lift_projector_and_field E.toRingEquiv hq ι faithful
  exact ⟨p, hp, j, congrArg Subtype.val he, hj, fun a => congrArg Subtype.val (hfield a), hunit⟩

end ZOverQ.Qualitative.Specialization

#print axioms ZOverQ.Qualitative.Specialization.biproduct_end_bijective_of_reference
#print axioms ZOverQ.Qualitative.Specialization.invariantSpecialization
#print axioms ZOverQ.Qualitative.Specialization.lift_projector_and_field
#print axioms ZOverQ.Qualitative.Specialization.rational_scalar_in_corner
#print axioms ZOverQ.Qualitative.Specialization.lift_invariant_projector_and_field
