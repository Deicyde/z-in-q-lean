import PicardDescent
import LocalSupport
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Extension of scalars for the proper Picard sextic and its unpointed Jacobian. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open ZInQBlueprint.BinaryCover ZInQBlueprint.SexticEmbedding
open ZOverQ.Qualitative.PicardDescent

namespace ZOverQ.Qualitative.PicardLocalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L]

private theorem open_pullback {S T : Scheme} (f : T ⟶ S) {U X : Over S} (j : U ⟶ X)
    (hj : IsOpenImmersion j.left) : IsOpenImmersion ((Over.pullback f).map j).left := by
  let m : pullback U.hom f ⟶ pullback X.hom f := ((Over.pullback f).map j).left
  have h : m ≫ pullback.snd X.hom f = pullback.snd U.hom f := ((Over.pullback f).map j).w
  have sq : IsPullback (pullback.fst U.hom f) m j.left (pullback.fst X.hom f) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd X.hom f) (v₂₂ := X.hom) (h₃₁ := f)
    · rw [h,j.w]; exact IsPullback.of_hasPullback _ _
    · symm; exact pullback.lift_fst ..
    · exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq hj

private theorem scalarStalks [Algebra K L] (f : K[X]) (deg : f.natDegree = 6) (sep : f.Separable)
    (x : (pullback (projectiveStructure (fun i : Fin 7 => f.coeff i)) (scalarMap K L) : Scheme)) :
    PreValuationRing ((pullback (projectiveStructure (fun i : Fin 7 => f.coeff i))
      (scalarMap K L)).presheaf.stalk x) := by
  let a : Fin 7 → K := fun i => f.coeff i
  let C := Over.mk (projectiveStructure a)
  let h := scalarMap K L
  let π := pullback.fst C.hom h
  let Y (i : Bool) := pullback (chartAsOver a i).left π
  let j (i : Bool) : Y i ⟶ _ := pullback.snd (chartAsOver a i).left π
  obtain ⟨i,y,hy⟩ := cover_projective a (π x)
  have rg : Set.range (j i) = π ⁻¹' Set.range (chartAsOver a i).left := Scheme.Pullback.range_snd _ _
  obtain ⟨v,hv⟩ := rg.ge ⟨y,hy⟩
  rw [← hv]
  let g := equationPolynomial (ZInQBlueprint.SexticEmbedding.coefficients a i)
  have ggood : 0 < g.natDegree ∧ g.Separable := by
    rw [show g = _ from polynomial_chart deg i]
    cases i
    · exact ⟨by change 0 < f.natDegree; omega,sep⟩
    · obtain ⟨⟨hg,_⟩,hs⟩ := reverse_sextic_regular deg sep
      exact ⟨by change 0 < f.reverse.natDegree; omega,hs⟩
  let G := g.map (algebraMap K L)
  have gd : 0 < G.natDegree := by
    rw [show G.natDegree = g.natDegree from natDegree_map_eq_of_injective (algebraMap K L).injective g]
    exact ggood.1
  let : Invertible (2 : L) := invertibleOfNonzero (by norm_num)
  let : IsDedekindDomain (Cover G) := dedekind_cover gd ggood.2.map
  let e : Y i ≅ (SpecOver (R := L) (Cover G)).left :=
    pullbackRightPullbackFstIso C.hom h (chartAsOver a i).left ≪≫
    pullback.congrHom (chartAsOver a i).w rfl ≪≫
    (Over.forget _).mapIso (affineBaseChange K L g).symm
  let : IsOpenImmersion (j i) := MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ π
    (inferInstanceAs (IsOpenImmersion (chartMap a i)))
  exact (open_stalk_prevaluation (j i) v).mpr
    ((open_stalk_prevaluation e.hom v).mp (affine_dedekind_stalk _ (e.hom v)))

/-- The proper four-quadric completion commutes with an arbitrary characteristic-zero field embedding. -/
def projectiveScalarExtension (φ : K →+* L) (f : K[X]) (deg : f.natDegree = 6) (sep : f.Separable) :
    (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      (Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))) ≅
        Over.mk (projectiveStructure (fun i : Fin 7 => (f.map φ).coeff i)) := by
  let : Algebra K L := φ.toAlgebra
  let g := f.map φ
  have dg : g.natDegree = 6 := (natDegree_map_eq_of_injective φ.injective f).trans deg
  have sg : g.Separable := sep.map
  let X := Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))
  let D := Over.mk (projectiveStructure (fun i : Fin 7 => g.coeff i))
  let h := Spec.map (CommRingCat.ofHom φ)
  let B := (Over.pullback h).obj X
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) AlgebraicGeometry.IsIntegral :=
    ⟨fun e _ => AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩
  let geo := geometric_integral_quadrics f deg sep
  let : AlgebraicGeometry.IsIntegral B.left :=
    (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := AlgebraicGeometry.IsIntegral) (R := K) (f := X.hom)).mp geo.1 L
  obtain ⟨hD,vD⟩ := projective_regular _ (sextic_charts_dedekind dg sg)
  let : AlgebraicGeometry.IsIntegral D.left := hD
  let : IsProper X.hom := proper_projectiveStructure _
  let : IsProper D.hom := proper_projectiveStructure _
  let : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd X.hom h))
  let A := SpecOver (R := L) (Cover g)
  let : Nonempty A.left := inferInstanceAs (Nonempty (Spec (.of (Cover g))))
  let e : A ≅ (Over.pullback h).obj (SpecOver (R := K) (Cover f)) := affineBaseChange K L f
  let j := (Over.pullback h).map (finiteChartMap deg)
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  let : IsOpenImmersion j.left := open_pullback h (finiteChartMap deg) inferInstance
  let i : A ⟶ B := e.hom ≫ j
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ j.left))
  exact (ZInQBlueprint.CurveExtension.unique_model_iso i (finiteChartMap dg)
    (scalarStalks (L := L) f deg sep) vD).exists.choose

private theorem geometry (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    SmoothOfRelativeDimension 1 (projectiveStructure (Picard.coefficients u v)) ∧
      GeometricallyIntegral (projectiveStructure (Picard.coefficients u v)) := by
  have deg := fibre_degree u v hv
  have sep := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0) hu hv hD
  have geo := geometric_integral_quadrics (PicardLocal.sextic u v) deg sep
  rw [polynomial_coefficients] at geo
  obtain ⟨hI,_,hs,hdim,_⟩ := sexticCompletion_geometry deg sep
  let M := sexticCompletion (PicardLocal.sextic u v) deg
  let : AlgebraicGeometry.IsIntegral M.left := hI
  let : Smooth M.hom := hs
  have hrel := ZInQBlueprint.SixJacobian.relative_dimension_one M.hom hdim
  let e := completionIso u v hu hv hD
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  refine ⟨?_,geo⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1) e.hom.left]
  change SmoothOfRelativeDimension 1 (e.hom.left ≫ (Over.mk (projectiveStructure (Picard.coefficients u v))).hom)
  rw [e.hom.w]
  exact hrel

/-- Scalar extension of the actual Picard Jacobian along any field embedding. -/
def jacobianScalarExtension (φ : K →+* L) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    (ZInQBlueprint.AbelianModel.baseChange φ).obj (jacobian u v hu hv hD) ≅
      jacobian (φ u) (φ v) ((map_ne_zero_iff φ φ.injective).mpr hu) ((map_ne_zero_iff φ φ.injective).mpr hv)
        (sub_ne_zero.mpr (φ.injective.ne (sub_ne_zero.mp hD))) := by
  let : Algebra K L := φ.toAlgebra
  let C := Over.mk (projectiveStructure (Picard.coefficients u v))
  let D := Over.mk (projectiveStructure (Picard.coefficients (φ u) (φ v)))
  let : IsProper C.hom := proper_projectiveStructure _
  let : IsProper D.hom := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 C.hom := (geometry u v hu hv hD).1
  let : GeometricallyIntegral C.hom := (geometry u v hu hv hD).2
  have gd := geometry (φ u) (φ v) ((map_ne_zero_iff φ φ.injective).mpr hu) ((map_ne_zero_iff φ φ.injective).mpr hv)
    (sub_ne_zero.mpr (φ.injective.ne (sub_ne_zero.mp hD)))
  let : SmoothOfRelativeDimension 1 D.hom := gd.1
  let : GeometricallyIntegral D.hom := gd.2
  have sep := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0) hu hv hD
  have e := projectiveScalarExtension φ (PicardLocal.sextic u v) (fibre_degree u v hv) sep
  have he : (PicardLocal.sextic u v).map φ = PicardLocal.sextic (φ u) (φ v) := by
    simp [PicardLocal.sextic,PicardLocal.quadratic,PicardLocal.quartic]
  rw [he,polynomial_coefficients u v,polynomial_coefficients (φ u) (φ v)] at e
  exact ZInQBlueprint.IntegralPicard.unpointed_baseChangeIso C D e

private theorem completion_geometry {f : K[X]} (deg : f.natDegree = 6) (sep : f.Separable) :
    let D := sexticCompletion f deg
    IsProper D.hom ∧ SmoothOfRelativeDimension 1 D.hom ∧ GeometricallyIntegral D.hom := by
  let D := sexticCompletion f deg
  let X := Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))
  obtain ⟨hI,hP,hS,hDim,_⟩ := sexticCompletion_geometry deg sep
  let : AlgebraicGeometry.IsIntegral D.left := hI
  let : Smooth D.hom := hS
  let e : D ≅ X := (completion_is_quadrics deg sep).exists.choose
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  refine ⟨hP,ZInQBlueprint.SixJacobian.relative_dimension_one D.hom hDim,?_⟩
  change GeometricallyIntegral D.hom
  rw [← e.hom.w, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
  exact geometric_integral_quadrics f deg sep

/-- The unpointed Jacobian of the canonical two-chart proper completion of the specified polynomial. -/
def completionJacobian (f : K[X]) (deg : f.natDegree = 6) (sep : f.Separable) :
    ZInQBlueprint.AbelianModel.GroupScheme K := by
  let D := sexticCompletion f deg
  let p := completion_geometry deg sep
  let : IsProper D.hom := p.1
  let : SmoothOfRelativeDimension 1 D.hom := p.2.1
  let : GeometricallyIntegral D.hom := p.2.2
  exact JacobianVarieties.Picard.Unpointed.groupScheme K D.hom

private def squareCompletionIso {f g : K[X]} (a : K) (ha : a ≠ 0) (hg : g = C (a^2) * f)
    (df : f.natDegree = 6) (sf : f.Separable) (dg : g.natDegree = 6) (sg : g.Separable) :
    Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i)) ≅ sexticCompletion g dg := by
  let X := Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))
  let D := sexticCompletion g dg
  let A := SpecOver (R := K) (Cover f)
  let B := SpecOver (R := K) (Cover g)
  let w : K[X]ˣ := Units.map C.toMonoidHom (Units.mk0 a ha)
  have hw : (AlgEquiv.refl : K[X] ≃ₐ[K] K[X]) g = (w : K[X])^2*f := by
    change g = (C a)^2*f
    rw [←map_pow,hg]
  let e : A ≅ B := specIso (squareEquiv (AlgEquiv.refl : K[X] ≃ₐ[K] K[X]) w hw)
  let j : A ⟶ X := finiteChartMap df
  let k : B ⟶ D := chartInclusion K g g.reverse (reverse_sextic_overlap dg) false
  let : Nonempty A.left := inferInstanceAs (Nonempty (Spec (.of (Cover f))))
  obtain ⟨hi,hv⟩ := projective_regular _ (sextic_charts_dedekind df sf)
  obtain ⟨di,dp,_,_,dv⟩ := sexticCompletion_geometry dg sg
  let : AlgebraicGeometry.IsIntegral X.left := hi
  let : AlgebraicGeometry.IsIntegral D.left := di
  let : IsProper X.hom := proper_projectiveStructure _
  let : IsProper D.hom := dp
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (finiteChartMap df).left)
  let : IsOpenImmersion k.left := chartInclusion_open ..
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  let : IsOpenImmersion (e.hom ≫ k).left := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ k.left))
  exact (ZInQBlueprint.CurveExtension.unique_model_iso j (e.hom ≫ k) hv dv).exists.choose

/-- Arbitrary field extension followed by a square ordinate change identifies the Jacobian
of the original Picard curve with the Jacobian of the actual smooth proper completion of `g`. -/
theorem jacobian_scalar_square (φ : K →+* L) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0)
    (g : L[X]) (w : L) (hw : w ≠ 0) (hg : g = C (w^2) * (PicardLocal.sextic u v).map φ) :
    ∃ (dg : g.natDegree = 6) (sg : g.Separable),
      Nonempty ((ZInQBlueprint.AbelianModel.baseChange φ).obj (jacobian u v hu hv hD) ≅
        completionJacobian g dg sg) := by
  let : Algebra K L := φ.toAlgebra
  let f := PicardLocal.sextic u v
  have df := fibre_degree u v hv
  have sf := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0) hu hv hD
  have dm : (f.map φ).natDegree = 6 := (natDegree_map_eq_of_injective φ.injective f).trans df
  have sm : (f.map φ).Separable := sf.map
  have dg : g.natDegree = 6 := by rw [hg,natDegree_C_mul (pow_ne_zero _ hw)]; exact dm
  have sg : g.Separable := hg ▸ Separable.unit_mul ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hw)).map C) sm
  let src := Over.mk (projectiveStructure (Picard.coefficients u v))
  let dst := sexticCompletion g dg
  let : IsProper src.hom := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 src.hom := (geometry u v hu hv hD).1
  let : GeometricallyIntegral src.hom := (geometry u v hu hv hD).2
  let p := completion_geometry dg sg
  let : IsProper dst.hom := p.1
  let : SmoothOfRelativeDimension 1 dst.hom := p.2.1
  let : GeometricallyIntegral dst.hom := p.2.2
  have e := projectiveScalarExtension φ (PicardLocal.sextic u v) df sf
  rw [polynomial_coefficients u v] at e
  exact ⟨dg,sg,⟨ZInQBlueprint.IntegralPicard.unpointed_baseChangeIso src dst
    (e ≪≫ squareCompletionIso w hw hg dm sm dg sg)⟩⟩

open ZInQ ZInQ.QualitativeHeight PicardConjugation in
private theorem primitive_parameters (t : ℚ) (ht : t ∉ contactSet) :
    let s := picardParameter t
    U s ≠ 0 ∧ V s ≠ 0 ∧ U s - V s ≠ 0 := by
  let s := picardParameter t
  let x : fixedField := s
  have ht0 : t ≠ 0 := by intro h; apply ht; rw [h]; decide
  have hn : x^2+3 ≠ 0 := by
    have h : ((s^2+3 : ℚ) : fixedField) ≠ 0 := Rat.cast_ne_zero.mpr (by positivity)
    push_cast at h
    exact h
  have hp : U s * V s ≠ 0 := by
    change (x+ρ)^6*(x-ρ)^6 ≠ 0
    rw [Picard.sixth_product x ρ rho_sq]
    exact pow_ne_zero _ hn
  have hb : branchForm s 1 ≠ 0 := by
    have e := branchForm_change ht0 1
    rw [mul_one] at e
    rw [show branchForm s 1 = _ from e]
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero one_ne_zero ht0))
      (mul_ne_zero (by norm_num) (Mult.contactPoly_ne_zero ht))
  have hrho : ρ ≠ 0 := by
    intro hz
    have h := rho_sq
    rw [hz] at h
    norm_num at h
  have eqn : U s - V s = 12*ρ*((branchForm s 1 : ℚ) : fixedField) := by
    rw [show U s - V s = _ from Picard.sixth_difference x ρ rho_sq]
    simp [branchForm,x]
  exact ⟨left_ne_zero_of_mul hp,right_ne_zero_of_mul hp,eqn ▸
    mul_ne_zero (mul_ne_zero (by norm_num) hrho) (Rat.cast_ne_zero.mpr hb)⟩

open ZInQ ZInQ.QualitativeHeight PicardConjugation in
private theorem primitive_twist_regular (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0) :
    let s := picardParameter t
    let a := U s/(2*(d:fixedField))
    let b := V s/(2*(d:fixedField))
    a ≠ 0 ∧ b ≠ 0 ∧ a-b ≠ 0 := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨hu,hv,hD⟩ := primitive_parameters t ht
  have nd : 2*(d:fixedField) ≠ 0 := mul_ne_zero (by norm_num) (Rat.cast_ne_zero.mpr hd)
  have ha : a ≠ 0 := div_ne_zero hu nd
  have hb : b ≠ 0 := div_ne_zero hv nd
  have he : a-b ≠ 0 := by
    change U s/_ - V s/_ ≠ 0
    rw [← sub_div]
    exact div_ne_zero hD nd
  exact ⟨ha,hb,he⟩


open ZInQ ZInQ.QualitativeHeight PicardConjugation in
/-- After any embedding of the fixed number field, the localized rational fibre is the genuine
Jacobian of the smooth completion of the primitive DDMM twist, including its exact ordinate scale. -/
theorem family_primitive_jacobian (φ : fixedField →+* L) (t : ℚ) (e : ℤ)
    (ht : t ∉ contactSet) (he : e ≠ 0) :
    let s := picardParameter t
    let f := LocalSupport.twisted s.num s.den e (φ ρ)
    ∃ (dg : f.natDegree = 6) (sg : f.Separable),
      Nonempty ((ZInQBlueprint.AbelianModel.baseChange φ).obj
        (familyJacobian t (e:ℚ) ht (by exact_mod_cast he) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)) ≅
          completionJacobian f dg sg) := by
  let s := picardParameter t
  let a := U s / (2*(e:fixedField))
  let b := V s / (2*(e:fixedField))
  have hd : (e:ℚ) ≠ 0 := by exact_mod_cast he
  have reg := primitive_twist_regular t (e:ℚ) ht hd
  change U s/(2*((e:ℚ):fixedField)) ≠ 0 ∧ V s/(2*((e:ℚ):fixedField)) ≠ 0 ∧
    U s/(2*((e:ℚ):fixedField)) - V s/(2*((e:ℚ):fixedField)) ≠ 0 at reg
  push_cast at reg
  obtain ⟨ha,hb,hD⟩ : a ≠ 0 ∧ b ≠ 0 ∧ a-b ≠ 0 := reg
  let f := LocalSupport.twisted s.num s.den e (φ ρ)
  obtain ⟨hw,hs⟩ := LocalSupport.primitive_chart_scale s e he (φ ρ)
  let w := 2*(e:L)*(s.den:L)^3
  have hm : (PicardLocal.sextic a b).map φ =
      PicardLocal.sextic (((s:L)+φ ρ)^6/(2*(e:L))) (((s:L)-φ ρ)^6/(2*(e:L))) := by
    rw [PicardLocal.sextic_map]
    simp [a,b,U,V,map_ofNat]
  have eqn : f = C (w^2) * (PicardLocal.sextic a b).map φ := by rw [hm]; exact hs
  obtain ⟨dg,sg,⟨i⟩⟩ := jacobian_scalar_square φ a b ha hb hD f w hw eqn
  refine ⟨dg,sg,⟨?_ ≪≫ i⟩⟩
  apply (ZInQBlueprint.AbelianModel.baseChange φ).mapIso
  apply eqToIso
  unfold familyJacobian
  simp only [Rat.cast_intCast]
  rfl

private theorem minpoly_radical {x : PicardConjugation.Qbar} (n : ℕ) (hn : 0 < n)
    (hx : x^2 = -(n : PicardConjugation.Qbar)) : minpoly ℚ x = (X^2 + C (n:ℚ)) := by
  let P : ℚ[X] := X^2 + C (n:ℚ)
  have hd : P.natDegree = 2 := by dsimp [P]; compute_degree!
  have hi : Irreducible P := irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide) (by
    intro a h
    have ha : a^2 + (n:ℚ) = 0 := by simpa [P,IsRoot] using h
    have hp : (0:ℚ) < n := by exact_mod_cast hn
    nlinarith [sq_nonneg a])
  apply (minpoly.eq_of_irreducible_of_monic hi ?_ (monic_X_pow_add_C (n:ℚ) (by decide : 2 ≠ 0))).symm
  simp [P,hx]

/-- A field containing both radicals admits an embedding of the fixed good field with the
specified image of `√−3`. This includes each finite Witt splitting field. -/
theorem coefficient_embedding (z q : L) (hz : z^2 = -2) (hq : q^2 = -3) :
    ∃ φ : PicardConjugation.fixedField →ₐ[ℚ] L, φ PicardConjugation.ρ = q := by
  let S : Set PicardConjugation.Qbar := {(PicardConjugation.r : PicardConjugation.Qbar),
    (PicardConjugation.ρ : PicardConjugation.Qbar)}
  have hs (y : L) (n : ℕ) (hy : y^2 = -(n:L)) :
      ((X^2+C (n:ℚ) : ℚ[X]).map (algebraMap ℚ L)).Splits := by
    have eqn : ((X^2+C (n:ℚ) : ℚ[X]).map (algebraMap ℚ L)) = (X-C y)*(X-C (-y)) := by
      rw [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,map_natCast,C_neg]
      have h : (C (n:L) : L[X]) = -(C y)^2 := by rw [← map_pow,hy,map_neg,neg_neg]
      rw [h]
      ring
    rw [eqn]
    exact (Splits.X_sub_C y).mul (Splits.X_sub_C (-y))
  have valpow (y : PicardConjugation.fixedField) (n : ℕ) (hy : y^2 = -(n : PicardConjugation.fixedField)) :
      (y : PicardConjugation.Qbar)^2 = -(n : PicardConjugation.Qbar) := by
    change (PicardConjugation.fixedField.val y)^2 = _
    rw [← map_pow,hy,map_neg,map_natCast]
  have m2 : minpoly ℚ (PicardConjugation.r : PicardConjugation.Qbar) = X^2 + C (2:ℚ) :=
    minpoly_radical 2 (by decide) (valpow PicardConjugation.r 2 (by simpa using PicardConjugation.r_sq))
  have m3 : minpoly ℚ (PicardConjugation.ρ : PicardConjugation.Qbar) = X^2 + C (3:ℚ) :=
    minpoly_radical 3 (by decide) (valpow PicardConjugation.ρ 3 (by simpa using PicardConjugation.rho_sq))
  have split : ∀ x ∈ S, IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ L)).Splits := by
    intro x hx
    refine ⟨Algebra.IsIntegral.isIntegral x,?_⟩
    rcases (Set.mem_insert_iff.mp hx) with rfl|h
    · rw [m2]; exact hs z 2 (by simpa using hz)
    · rw [Set.mem_singleton_iff.mp h,m3]; exact hs q 3 (by simpa using hq)
  have root : aeval q (minpoly ℚ (PicardConjugation.ρ : PicardConjugation.Qbar)) = 0 := by rw [m3]; simp [hq]
  exact IntermediateField.exists_algHom_adjoin_of_splits_of_aeval (S := S) split
    PicardConjugation.ρ.property root

open LocalSupport PicardConjugation PicardLocal
open ZInQ ZInQ.QualitativeHeight

private abbrev finiteWittCharZero (p : ℕ) [Fact p.Prime] (F : Subfield (Residues p)) :
    CharZero (WittVector p F) :=
  charZero_of_injective_ringHom (f := fromPadics p F)
    ((WittVector.map_injective _ (ZMod.castHom (by simp) F).injective).comp (WittVector.equiv p).symm.injective)

private theorem map_twisted {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (a b e : ℤ) (q : A) : (twisted a b e q).map φ = twisted a b e (φ q) := by
  simp [twisted,PicardLocal.sextic_map,upper,lower,map_ofNat]

private theorem twist_nonzero (s : ℚ) : (PrimitiveTwist.twist s : ℤ) ≠ 0 := by
  exact_mod_cast (PrimitiveTwist.positive s).ne'

/-- Comparison over the fraction field of the exact Witt ring in the splitting data.
The polynomial in the target is literally the generic fibre of its integral DDMM polynomial. -/
def WittComparison {p : ℕ} [Fact p.Prime] (t : ℚ) (e : ℤ) (ht : t ∉ contactSet) (he : e ≠ 0)
    {q : WittRing p} (D : FiniteSplitting p (picardParameter t).num (picardParameter t).den e q) : Prop :=
  letI : Finite D.field := D.finite
  letI := finiteWittCharZero p D.field
  let S := WittVector p D.field
  let L := FractionRing S
  let s := picardParameter t
  let f := (twisted s.num s.den e D.rho).map (algebraMap S L)
  ∃ (φ : fixedField →ₐ[ℚ] L), φ ρ = algebraMap S L D.rho ∧
    ∃ (df : f.natDegree = 6) (sf : f.Separable),
      Nonempty ((ZInQBlueprint.AbelianModel.baseChange φ.toRingHom).obj
        (familyJacobian t (e:ℚ) ht (by exact_mod_cast he) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)) ≅
          completionJacobian f df sf)

/-- The finite unramified splitting data identify the localized global Jacobian with the
Jacobian of the smooth completion of their own integral polynomial, with the specified `ρ`. -/
theorem finite_splitting_jacobian (p : ℕ) [Fact p.Prime] (hp : 3 < p) (t : ℚ) (e : ℤ)
    (ht : t ∉ contactSet) (he : e ≠ 0) {q : WittRing p} (hq : q^2 = -3)
    (D : FiniteSplitting p (picardParameter t).num (picardParameter t).den e q) :
    WittComparison t e ht he D := by
  let : Finite D.field := D.finite
  let : CharZero (WittVector p D.field) := finiteWittCharZero p D.field
  let S := WittVector p D.field
  let E := FractionRing S
  let ι := algebraMap S E
  have hrho : D.rho^2 = -3 := by
    apply inclusion_injective p D.field
    rw [map_pow,D.inclusion_rho,hq,map_neg,map_ofNat]
  obtain ⟨z,hz⟩ := reciprocal_radical p hp D
  obtain ⟨φ,hφ⟩ := coefficient_embedding (ι z) (ι D.rho)
    (by rw [← map_pow,hz,map_neg,map_ofNat]) (by rw [← map_pow,hrho,map_neg,map_ofNat])
  refine ⟨φ,hφ,?_⟩
  let s := picardParameter t
  have eqn : (twisted s.num s.den e D.rho).map ι = twisted s.num s.den e (φ ρ) := by
    rw [hφ]
    exact map_twisted ι _ _ _ _
  rw [show (twisted (picardParameter t).num (picardParameter t).den e D.rho).map
    (algebraMap S E) = _ from eqn]
  exact family_primitive_jacobian φ.toRingHom t e ht he

/-- For every prime `p > 3` with even branch valuation, one cluster picture, one finite
unramified splitting ring and its actual generic sextic realize the same localized Jacobian. -/
theorem family_local_cluster_jacobian (p : ℕ) [Fact p.Prime] (hp : 3 < p) (t : ℚ)
    (ht : t ∉ contactSet) (hev : ¬ Odd (padicValRat p (primitiveBranch (picardParameter t)))) :
    let s := picardParameter t
    let e : ℤ := PrimitiveTwist.twist s
    ∃ (q : WittRing p) (A : Finset (Fin 2)) (m : ℕ) (D : FibreData p s.num s.den e q A m),
      q^2 = -3 ∧ WittComparison t e ht (twist_nonzero s) D.finiteModel := by
  let s := picardParameter t
  let e : ℤ := PrimitiveTwist.twist s
  have he : e ≠ 0 := twist_nonzero s
  obtain ⟨q₀,h₀⟩ := PrimitiveTwist.exists_rho p hp
  obtain ⟨q,sign,A,m,⟨D⟩⟩ := rational_fibre_data p hp s (primitiveBranch_ne_zero ht) hev h₀
  have hq : q^2 = -3 := by rcases sign with rfl|rfl <;> simpa using h₀
  exact ⟨q,A,m,D,hq,finite_splitting_jacobian p hp t e ht he hq D.finiteModel⟩

#print axioms finite_splitting_jacobian
#print axioms family_local_cluster_jacobian

#print axioms coefficient_embedding

#print axioms family_primitive_jacobian

#print axioms completionJacobian
#print axioms jacobian_scalar_square
#print axioms projectiveScalarExtension
#print axioms jacobianScalarExtension

end
end ZOverQ.Qualitative.PicardLocalization
