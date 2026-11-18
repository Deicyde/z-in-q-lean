import QuadraticAction
import AbelianModel
import UniformDescent
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Descent of the isogeny supplied by Guitart's Proposition 2.10.
The action on a geometric homomorphism is actual pullback of group schemes.
The equation restricted to automorphisms fixing the field of complete
definition has the normalized diagonal intertwiner equal to the identity. -/

namespace ZOverQ.Qualitative.GuitartDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZInQBlueprint
open CategoryTheory.Functor MonoidalCategory MonObj
open NormalDescent AbelianModel
open scoped NormalDescent TensorProduct CategoryTheory.Obj

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

section Geometric
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
local notation "F" => Over.pullback (specExtension K Ω)
local notation "FB" => baseChange (algebraMap K Ω)

/-- The canonical comparison for scalar conjugation. This geometric construction
also occurs in ZInQBlueprint.QuaternionMarking.GaloisComparison. -/
private abbrev S (σ : Ω ≃ₐ[K] Ω) := Spec.map (CommRingCat.ofHom σ.toRingHom)
private abbrev G (σ : Ω ≃ₐ[K] Ω) := Over.pullback (S σ)

private theorem deck_inverse (X : Over (Spec (.of K))) (σ : Ω ≃ₐ[K] Ω) :
    deck X.hom σ ≫ deck X.hom σ.symm = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc,deck_snd,deck_snd_assoc,Category.id_comp,← Spec.map_comp]
    have id : CommRingCat.ofHom σ.symm.toRingHom ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
      ext x
      exact σ.apply_symm_apply x
    rw [id, Spec.map_id, Category.comp_id]

private def component (X : Over (Spec (.of K))) (σ : Ω ≃ₐ[K] Ω) :
    (F).obj X ≅ (G σ).obj ((F).obj X) := by
  let A := (F).obj X
  let f : A.left ⟶ pullback A.hom (S σ) := pullback.lift (deck X.hom σ) A.hom (deck_snd X.hom σ)
  let : IsIso (deck X.hom σ) := ⟨deck X.hom σ.symm, deck_inverse X σ, deck_inverse X σ.symm⟩
  let : IsIso (S σ) := inferInstanceAs (IsIso ((Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op).hom))
  let : IsIso f := IsIso.of_isIso_fac_right (show f ≫ pullback.fst A.hom (S σ) = deck X.hom σ from pullback.lift_fst ..)
  exact Over.isoMk (asIso f) (pullback.lift_snd ..)

private theorem component_fst (X : Over (Spec (.of K))) (σ : Ω ≃ₐ[K] Ω) :
    (component X σ).hom.left ≫ pullback.fst _ _ = deck X.hom σ := pullback.lift_fst ..

private theorem component_snd (X : Over (Spec (.of K))) (σ : Ω ≃ₐ[K] Ω) :
    (component X σ).hom.left ≫ pullback.snd _ _ = ((F).obj X).hom := pullback.lift_snd ..

private theorem deck_naturality {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (σ : Ω ≃ₐ[K] Ω) :
    ((F).map f).left ≫ deck Y.hom σ = deck X.hom σ ≫ ((F).map f).left := by
  apply pullback.hom_ext
  · simp [Over.pullback_map_left]
  · simp [Over.pullback_map_left]

private def rationalComparison (σ : Ω ≃ₐ[K] Ω) : F ≅ F ⋙ G σ :=
  NatIso.ofComponents (fun X => component X σ) fun {X Y} f => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((F).map f).left ≫ (component Y σ).hom.left) ≫ _ = ((component X σ).hom.left ≫ ((G σ).map ((F).map f)).left) ≫ _
      simp only [Category.assoc, component_fst, G, Over.pullback_map_left, pullback.lift_fst, ← Category.assoc (component X σ).hom.left, component_fst]
      exact deck_naturality f σ
    · change (((F).map f).left ≫ (component Y σ).hom.left) ≫ _ = ((component X σ).hom.left ≫ ((G σ).map ((F).map f)).left) ≫ _
      simp only [Category.assoc,component_snd, G, Over.pullback_map_left, pullback.lift_snd]
      exact ((F).map f).w

private def rationalGroupComparison (A : GroupScheme K) (σ : Ω ≃ₐ[K] Ω) :
    (F).mapCommGrp.obj A ≅ (G σ).mapCommGrp.obj ((F).mapCommGrp.obj A) :=
  (Functor.mapCommGrpNatIso (rationalComparison σ)).app A ≪≫ Functor.mapCommGrpCompIso.app A

private theorem comparison_fst (A : GroupScheme K) (σ : Ω ≃ₐ[K] Ω) :
    (rationalGroupComparison A σ).hom.hom.hom.hom.left ≫ pullback.fst _ _ = deck A.X.hom σ := by
  change ((component A.X σ).hom.left ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  exact pullback.lift_fst ..


private theorem sliceHom_descent [CharZero K] [Normal K Ω]
    {A B : Over (Spec (.of K))} [LocallyOfFiniteType A.hom] [IsReduced A.left] [IsSeparated B.hom]
    (f : (F).obj A ⟶ (F).obj B)
    (invariant : ∀ σ : Ω ≃ₐ[K] Ω, deck A.hom σ ≫ f.left = f.left ≫ deck B.hom σ) :
    ∃! g : A ⟶ B, (F).map g = f := by
  let a := specExtension K Ω
  let p := pullback.fst A.hom a
  let q := pullback.fst B.hom a
  have hfw : f.left ≫ pullback.snd B.hom a = pullback.snd A.hom a := Over.w f
  have hf : (f.left ≫ q) ≫ B.hom = p ≫ A.hom := by
    rw [Category.assoc, pullback.condition (f := B.hom), ← Category.assoc, hfw,
      ← pullback.condition (f := A.hom)]
  have hi (σ : Ω ≃ₐ[K] Ω) : deck A.hom σ ≫ f.left ≫ q = f.left ≫ q := by
    rw [← Category.assoc, invariant, Category.assoc, deck_fst]
  obtain ⟨h,⟨hs,hp⟩,_⟩ := existsUnique_of_galois A.hom B.hom (f.left ≫ q) hf hi
  let g : A ⟶ B := Over.homMk h hs
  have hg : (F).map g = f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (show ((F).map g).left ≫ q = p ≫ h from pullback.lift_fst ..).trans hp
    · exact (show ((F).map g).left ≫ pullback.snd B.hom a = pullback.snd A.hom a from
        pullback.lift_snd ..).trans hfw.symm
  let : (F).Faithful := faithful_scalar_extension
  exact ⟨g,hg, fun z hz => (F).map_injective (hz.trans hg.symm)⟩

/-- Normal descent of an actual homomorphism between two different group schemes. -/
theorem groupHom_descent [CharZero K] [Normal K Ω]
    {A B : GroupScheme K} [LocallyOfFiniteType A.X.hom] [IsReduced A.X.left] [IsSeparated B.X.hom]
    (f : (FB).obj A ⟶ (FB).obj B)
    (invariant : ∀ σ : Ω ≃ₐ[K] Ω, deck A.X.hom σ ≫ f.hom.hom.hom.left =
      f.hom.hom.hom.left ≫ deck B.X.hom σ) :
    ∃! g : A ⟶ B, (FB).map g = f := by
  let : (F).Faithful := faithful_scalar_extension
  obtain ⟨g,hg,_⟩ := sliceHom_descent f.hom.hom.hom invariant
  have hm : IsMonHom ((F).map g) := by rw [hg]; exact f.hom.hom.isMonHom_hom
  let : IsMonHom g := isMonHom_of_map (F) g hm
  let h : A ⟶ B := InducedCategory.homMk (Grp.homMk g)
  have hh : (FB).map h = f := InducedCategory.hom_ext (Grp.hom_ext _ _ hg)
  exact ⟨h,hh, fun z hz => (FB).map_injective (hz.trans hh.symm)⟩

/-- The actual Galois conjugate of a scalar-extended group scheme homomorphism,
using the canonical comparisons on the source and target. -/
def conjugate {A B : GroupScheme K} (f : (FB).obj A ⟶ (FB).obj B) (σ : Ω ≃ₐ[K] Ω) :
    (FB).obj A ⟶ (FB).obj B :=
  (rationalGroupComparison A σ).hom ≫ (baseChange σ.toRingHom).map f ≫
    (rationalGroupComparison B σ).inv

theorem conjugate_deck {A B : GroupScheme K} (f : (FB).obj A ⟶ (FB).obj B) (σ : Ω ≃ₐ[K] Ω) :
    deck A.X.hom σ ≫ f.hom.hom.hom.left =
      (conjugate f σ).hom.hom.hom.left ≫ deck B.X.hom σ := by
  let ca := rationalGroupComparison A σ
  let cb := rationalGroupComparison B σ
  have h : ca.hom ≫ (baseChange σ.toRingHom).map f = conjugate f σ ≫ cb.hom := by
    simp [conjugate,ca,cb]
  have e := congrArg (fun w => w.hom.hom.hom.left ≫ pullback.fst _ _) h
  change (ca.hom.hom.hom.hom.left ≫ ((Over.pullback (Spec.map
      (CommRingCat.ofHom σ.toRingHom))).map f.hom.hom.hom).left) ≫ pullback.fst _ _ =
    ((conjugate f σ).hom.hom.hom.left ≫ cb.hom.hom.hom.hom.left) ≫ pullback.fst _ _ at e
  let sa := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let pa := pullback.fst ((FB).obj A).X.hom sa
  let pb := pullback.fst ((FB).obj B).X.hom sa
  let u := ((Over.pullback sa).map f.hom.hom.hom).left
  have hu : u ≫ pb = pa ≫ f.hom.hom.hom.left := pullback.lift_fst ..
  have ha : ca.hom.hom.hom.hom.left ≫ pa = deck A.X.hom σ := comparison_fst A σ
  have hb : cb.hom.hom.hom.hom.left ≫ pb = deck B.X.hom σ := comparison_fst B σ
  calc
    _ = (ca.hom.hom.hom.hom.left ≫ pa) ≫ f.hom.hom.hom.left := by rw [ha]
    _ = ca.hom.hom.hom.hom.left ≫ u ≫ pb := by rw [hu,Category.assoc]
    _ = (conjugate f σ).hom.hom.hom.left ≫ cb.hom.hom.hom.hom.left ≫ pb := by
      simpa only [Category.assoc] using e
    _ = _ := by rw [hb]

/-- Nonzero integer multiplication on an abelian variety is finite, flat and
surjective (Milne, Abelian Varieties, Theorem 8.2 and Proposition 20.7).
Any such group homomorphism is an epimorphism in the category of group schemes. -/
theorem epi_of_finite_flat {A B : GroupScheme K} (f : A ⟶ B)
    [IsFinite f.hom.hom.hom.left] [Flat f.hom.hom.hom.left] [Surjective f.hom.hom.hom.left] :
    Epi f := by
  let : EffectiveEpi f.hom.hom.hom.left := inferInstance
  constructor
  intro Z g h eq
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi f.hom.hom.hom.left).mp (congrArg (fun w => w.hom.hom.hom.left) eq)

/-- A geometric isogeny that descends as a group homomorphism remains
finite and surjective over the ground field. -/
theorem finite_surjective_of_baseChange {A B : GroupScheme K}
    (proper : IsProper A.X.hom) (separated : IsSeparated B.X.hom) (f : A ⟶ B)
    (finite : IsFinite ((FB).map f).hom.hom.hom.left)
    (surj : Surjective ((FB).map f).hom.hom.hom.left) :
    IsFinite f.hom.hom.hom.left ∧ Surjective f.hom.hom.hom.left := by
  let a := specExtension K Ω
  let p := pullback.fst A.X.hom a
  let q := pullback.fst B.X.hom a
  let g := f.hom.hom.hom
  let j := ((F).map g).left
  have hq₀ := ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K Ω))).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  let : Surjective a := hq₀
  let : Surjective q := inferInstanceAs (Surjective (pullback.fst B.X.hom a))
  let : IsFinite j := finite
  let : Surjective j := surj
  have pf : j ≫ q = p ≫ g.left := pullback.lift_fst ..
  have ps : j ≫ pullback.snd B.X.hom a = pullback.snd A.X.hom a := pullback.lift_snd ..
  have hs : IsPullback j p q g.left := by
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback B.X.hom a).flip
    · rw [ps,g.w]
      exact (IsPullback.of_hasPullback A.X.hom a).flip
    · exact pf
  have hg : Surjective g.left := by
    constructor
    intro y
    obtain ⟨y',rfl⟩ := q.surjective y
    obtain ⟨x,rfl⟩ := j.surjective y'
    exact ⟨p x, (congrArg (fun t => t x) hs.w).symm⟩
  let : IsSeparated B.X.hom := separated
  let : IsProper (g.left ≫ B.X.hom) := g.w.symm ▸ proper
  let : IsProper g.left := IsProper.of_comp _ B.X.hom
  have : LocallyQuasiFinite g.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    obtain ⟨y',rfl⟩ := q.surjective y
    apply ((j.finite_preimage_singleton y').image p).subset
    intro x hx
    have hx' : q y' = g.left x := (Set.mem_singleton_iff.mp hx).symm
    obtain ⟨z,hz,hx⟩ := Scheme.exists_preimage_of_isPullback hs y' x hx'
    exact ⟨z,hz,hx⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, hg⟩

end Geometric

section Rational
variable {C : Type*} [Category* C] [Preadditive C] {U V : C}

/-- For abelian varieties all nonzero integer multiplications are epimorphisms.
This implies injectivity of a genuine Hom group into its rationalization. -/
theorem hom_rat_injective (multiply_epi : ∀ z : ℤ, z ≠ 0 → Epi (z • 𝟙 U)) :
    Function.Injective (fun f : U ⟶ V => (1:ℚ) ⊗ₜ[ℤ] f) := by
  let : Module.IsTorsionFree ℤ (U ⟶ V) := Module.IsTorsionFree.of_smul_eq_zero (by
    intro z f eq
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      let := multiply_epi z hz
      apply (cancel_epi (z • 𝟙 U)).mp
      simpa only [Preadditive.zsmul_comp, Category.id_comp, HasZeroMorphisms.comp_zero] using eq)
  exact Module.Flat.tensorProduct_mk_injective ℤ (U ⟶ V) ℚ

/-- Postcomposition by an ordinary homomorphism, extended to rational
endomorphisms of its source. -/
def afterHom (f : U ⟶ V) :
    (ℚ ⊗[ℤ] End U) →ₗ[ℤ] (ℚ ⊗[ℤ] (U ⟶ V)) :=
  TensorProduct.map LinearMap.id
    ((Preadditive.rightComp U f).comp End.addEquiv.toAddMonoidHom).toIntLinearMap

theorem afterHom_one (f : U ⟶ V) : afterHom f 1 = (1:ℚ) ⊗ₜ[ℤ] f := by
  change afterHom f ((1:ℚ) ⊗ₜ[ℤ] (1 : End U)) = _
  simp [afterHom]
  exact congrArg (fun z => (1:ℚ) ⊗ₜ[ℤ] z) (Category.id_comp f)

end Rational

section SplittingLaw

open UniformDescent
variable (M : FiniteGaloisIntermediateField ℚ Qbar)

theorem restriction_of_fixes (σ : Gal(Qbar/M)) :
    restriction M (σ.restrictScalars ℚ) = 1 := by
  ext x
  exact (AlgEquiv.restrictNormalHom_apply M.toIntermediateField (σ.restrictScalars ℚ) x).trans
    (σ.commutes x)

theorem coefficientUnit_at_fixes
    (b : Gal(M/ℚ) → Qbarˣ) (c : Gal(M/ℚ) × Gal(M/ℚ) → ℚˣ) (hc : c (1,1) = 1)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) (σ : Gal(Qbar/M)) :
    coefficientUnit b (restriction M (σ.restrictScalars ℚ)) = 1 := by
  rw [restriction_of_fixes]
  have h : b 1 = 1 := by simpa [hc] using (hb 1 1).symm
  exact Units.ext (Subtype.ext (congrArg Units.val h))

local notation "F" => baseChange (algebraMap M Qbar)

/-- Guitart, Prop. 2.10, restricted to the automorphisms fixing the field
over which the conjugate isogenies and splitting cochain factor. On this
subgroup the normalized diagonal intertwiner is the identity. The remaining
law is a literal equality in the rationalization of geometric Hom. -/
theorem isogeny_of_splitting_law
    {A B : GroupScheme M} [LocallyOfFiniteType A.X.hom] [IsReduced A.X.left]
    (proper : IsProper A.X.hom) (separated : IsSeparated B.X.hom)
    (b : Gal(M/ℚ) → Qbarˣ) (c : Gal(M/ℚ) × Gal(M/ℚ) → ℚˣ) (hc : c (1,1) = 1)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h))
    (φ : coefficientField b →ₐ[ℚ] (ℚ ⊗[ℤ] End ((F).obj A)))
    (κ : (F).obj A ⟶ (F).obj B)
    (finite : IsFinite κ.hom.hom.hom.left) (surj : Surjective κ.hom.hom.hom.left)
    (multiples : ∀ z : ℤ, z ≠ 0 →
      let nz := (z • 𝟙 ((F).obj A)).hom.hom.hom.left
      IsFinite nz ∧ Flat nz ∧ Surjective nz)
    (law : ∀ σ : Gal(Qbar/M), (1:ℚ) ⊗ₜ[ℤ] (conjugate κ σ) = afterHom κ
      (φ (↑((coefficientUnit b (restriction M (σ.restrictScalars ℚ)))⁻¹) : coefficientField b))) :
    ∃! f : A ⟶ B, (F).map f = κ ∧ IsFinite f.hom.hom.hom.left ∧ Surjective f.hom.hom.hom.left := by
  have multiply_epi (z : ℤ) (hz : z ≠ 0) : Epi (z • 𝟙 ((F).obj A)) := by
    obtain ⟨hf,hu,hs⟩ := multiples z hz
    exact epi_of_finite_flat _
  have fixed (σ : Gal(Qbar/M)) : conjugate κ σ = κ := by
    apply hom_rat_injective multiply_epi
    simpa only [coefficientUnit_at_fixes M b c hc hb σ, inv_one, Units.val_one, map_one,
      afterHom_one] using law σ
  let : IsSeparated B.X.hom := separated
  obtain ⟨f,hf,huniq⟩ := groupHom_descent κ fun σ => by
    simpa only [fixed] using conjugate_deck κ σ
  obtain ⟨hfin,honto⟩ := finite_surjective_of_baseChange (Ω := Qbar) proper separated f
    (hf.symm ▸ finite) (hf.symm ▸ surj)
  exact ⟨f,⟨hf,hfin,honto⟩, fun g hg => huniq g hg.1⟩

end SplittingLaw

/-- A nonsquare central scalar that is the square of a represented
endomorphism produces a coefficient field of twice the rational degree. -/
theorem quadratic_field_action {E A : Type} [Field E] [NumberField E] [Ring A]
    [Nontrivial A] [Algebra E A] [Algebra ℚ A] [IsScalarTower ℚ E A]
    (d : E) (ns : ¬ IsSquare d) (u : A) (hu : u*u = algebraMap E A d) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L),
      Module.finrank ℚ L = 2 * Module.finrank ℚ E ∧ Nonempty (L →ₐ[ℚ] A) := by
  let : Fact (¬ IsSquare d) := ⟨ns⟩
  let L := QuadraticAlgebra E d 0
  let : FiniteDimensional ℚ L := Module.Finite.trans E L
  let : NumberField L := {}
  let j : L →ₐ[E] A := QuadraticAlgebra.lift ⟨u, by simpa [Algebra.smul_def] using hu⟩
  refine ⟨L,inferInstance,inferInstance,?_,⟨j.restrictScalars ℚ⟩⟩
  rw [← Module.finrank_mul_finrank ℚ E L, mul_comm]
  exact congrArg (· * Module.finrank ℚ E) (QuadraticAlgebra.finrank_eq_two d 0)

end
end ZOverQ.Qualitative.GuitartDescent
#print axioms ZOverQ.Qualitative.GuitartDescent.groupHom_descent
#print axioms ZOverQ.Qualitative.GuitartDescent.conjugate_deck
#print axioms ZOverQ.Qualitative.GuitartDescent.finite_surjective_of_baseChange
#print axioms ZOverQ.Qualitative.GuitartDescent.hom_rat_injective
#print axioms ZOverQ.Qualitative.GuitartDescent.restriction_of_fixes
#print axioms ZOverQ.Qualitative.GuitartDescent.coefficientUnit_at_fixes
#print axioms ZOverQ.Qualitative.GuitartDescent.isogeny_of_splitting_law
#print axioms ZOverQ.Qualitative.GuitartDescent.quadratic_field_action
#print axioms ZOverQ.Qualitative.GuitartDescent.epi_of_finite_flat
