import ProjectiveSextic
import PicardConjugation
import PicardSextic
import PicardLocal
import UnpointedBaseChange

/-! The coefficient conjugation acts on the entire proper four-quadric model
of the Picard sextic by a linear transformation of projective four-space. -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open ZInQBlueprint.SexticEmbedding

namespace ZOverQ.Qualitative.PicardDescent

noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [CharZero K]
local notation "c" => Picard.coefficients
private abbrev grading (u v : K) := (equationsIdeal (c u v)).quotientGrading

private def perm : Fin 5 → Fin 5 := ![3,2,1,0,4]
private def weight (r : K) : Fin 5 → K := ![2*r,-r,r/2,-r/4,1]
private def relPerm : Fin 4 → Fin 4 := ![2,1,0,3]
private def relWeight : Fin 4 → K := ![-2,1,-1/2,1]

private theorem perm_sq (i : Fin 5) : perm (perm i) = i := by fin_cases i <;> rfl

private theorem weight_sq (r : K) (hr : r^2 = -2) (i : Fin 5) :
    weight r i * weight r (perm i) = 1 := by
  fin_cases i <;> simp [weight,perm] <;> linear_combination -(1/2)*hr

private def subVars (r : K) (i : Fin 5) : Variables K := C (weight r i) * X (perm i)
private def substitution (r : K) : Variables K →ₐ[K] Variables K := aeval (subVars r)

/-- Substitution takes each of the four defining quadrics to a scalar multiple
of the corresponding quadric for the swapped coefficients. -/
private theorem substitution_quadrics (u v r : K) (hr : r^2 = -2) (j : Fin 4) :
    substitution r (quadrics (c u v) j) =
      C (relWeight j) * quadrics (c v u) (relPerm j) := by
  change aeval (subVars r) (quadrics _ j) = _
  rw [eval_quadrics]
  apply MvPolynomial.funext
  intro a
  change eval a (generators (C ∘ c u v) (subVars r) j) =
    eval a (C (relWeight j) * generators (C ∘ c v u) X (relPerm j))
  rw [map_generators,map_mul,eval_C,map_generators]
  have coeffs (b e : K) : (eval a) ∘ (C ∘ c b e) = c b e := by
    funext i
    exact eval_C _
  have vars : (eval a) ∘ (X : Fin 5 → Variables K) = a := _root_.funext (fun i => eval_X i)
  have lin : (eval a) ∘ subVars r = fun i => weight r i * a (perm i) := by
    funext i
    simp [subVars]
  rw [coeffs,coeffs,vars,lin]
  fin_cases j
  · change (2*r*a 3)*(r/2*a 1) - (-r*a 2)^2 = -2*(a 1*a 3-(a 2)^2)
    linear_combination (a 1*a 3-(a 2)^2)*hr
  · change (2*r*a 3)*(-r/4*a 0) - (-r*a 2)*(r/2*a 1) = 1*(a 0*a 3-a 1*a 2)
    linear_combination -(a 0*a 3-a 1*a 2)/2*hr
  · change (-r*a 2)*(-r/4*a 0) - (r/2*a 1)^2 = (-1/2)*(a 0*a 2-(a 1)^2)
    linear_combination (a 0*a 2-(a 1)^2)/4*hr
  · change (1*a 4)^2 - quadratic (c u v) (2*r*a 3) (-r*a 2) (r/2*a 1) (-r/4*a 0) =
      1*((a 4)^2-quadratic (c v u) (a 0) (a 1) (a 2) (a 3))
    dsimp [quadratic,Picard.coefficients]
    ring_nf
    rw [hr]
    ring

private def coordinateHom (u v r : K) (hr : r^2 = -2) :
    CoordRing (c u v) →ₐ[K] CoordRing (c v u) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K _).comp (substitution r)) fun p hp => by
    have le : (equationsIdeal (c u v)).toIdeal ≤
        RingHom.ker ((Ideal.Quotient.mkₐ K (equationsIdeal (c v u)).toIdeal).comp (substitution r)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change Ideal.Quotient.mk _ (substitution r (quadrics (c u v) j)) = 0
      rw [substitution_quadrics _ _ _ hr]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self _))
    exact le hp

private theorem coordinateHom_apply (u v r : K) (hr : r^2 = -2) (i : Fin 5) :
    coordinateHom u v r hr (coord (c u v) i) =
      algebraMap K _ (weight r i) * coord (c v u) (perm i) := by
  change Ideal.Quotient.mk _ (aeval (subVars r) (X i)) = _
  rw [aeval_X]
  exact map_mul (Ideal.Quotient.mk _) _ _

private theorem coordinateHom_comp (u v r : K) (hr : r^2 = -2) :
    (coordinateHom v u r hr).comp (coordinateHom u v r hr) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change coordinateHom v u r hr (coordinateHom u v r hr (coord (c u v) i)) = coord _ i
  rw [coordinateHom_apply,map_mul,AlgHom.commutes,coordinateHom_apply,← mul_assoc,← map_mul,
    weight_sq _ hr, map_one,one_mul,perm_sq]

private def gradedHom (u v r : K) (hr : r^2 = -2) : grading u v →+*ᵍ grading v u where
  __ := (coordinateHom u v r hr).toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p,hp,rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp hx
    change Ideal.Quotient.mk _ (substitution r p) ∈ _
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    rw [mem_homogeneousSubmodule]
    have hh : p.IsHomogeneous n := hp
    simpa only [one_mul,substitution] using hh.aeval (subVars r)
      (fun i => (isHomogeneous_X K (perm i)).C_mul (weight r i))

private theorem gradedHom_comp (u v r : K) (hr : r^2 = -2) :
    (gradedHom v u r hr).comp (gradedHom u v r hr) = GradedRingHom.id (grading u v) := by
  ext x
  exact DFunLike.congr_fun (coordinateHom_comp u v r hr) x

private theorem gradedHom_surjective (u v r : K) (hr : r^2 = -2) :
    Function.Surjective (gradedHom u v r hr) := by
  intro x
  exact ⟨gradedHom v u r hr x, DFunLike.congr_fun (gradedHom_comp v u r hr) x⟩

private def projHom (u v r : K) (hr : r^2 = -2) :
    fourQuadricsProj (c v u) ⟶ fourQuadricsProj (c u v) :=
  Proj.map (gradedHom u v r hr)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (gradedHom_surjective u v r hr))

private theorem projHom_comp (u v r : K) (hr : r^2 = -2) :
    projHom v u r hr ≫ projHom u v r hr = 𝟙 _ := by
  unfold projHom
  rw [← Proj.map_comp]
  have h := gradedHom_comp u v r hr
  simpa only [h] using (Proj.map_id (𝒜 := grading u v))

/-- Conjugation on the entire scheme of four quadrics is induced by
[A:B:C:D:T] ↦ [2rD:−rC:rB/2:−rA/4:T], where r²=−2. -/
def projectiveIso (u v r : K) (hr : r^2 = -2) :
    fourQuadricsProj (c v u) ≅ fourQuadricsProj (c u v) where
  hom := projHom u v r hr
  inv := projHom v u r hr
  hom_inv_id := projHom_comp v u r hr
  inv_hom_id := projHom_comp u v r hr

set_option maxHeartbeats 1200000 in
private theorem projHom_over (u v r : K) (hr : r^2 = -2) :
    projHom u v r hr ≫ projectiveStructure (c u v) = projectiveStructure (c v u) := by
  let f := gradedHom u v r hr
  let hf := HomogeneousIdeal.irrelevant_le_map_of_surjective f (gradedHom_surjective u v r hr)
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι _ _ _ _ ≫ (Proj.map f hf ≫ (Proj.toSpecZero (grading u v) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K _)))) =
    Proj.awayι _ _ _ _ ≫ (Proj.toSpecZero (grading v u) ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)))
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 _ s.2.2]
  simp only [Category.assoc,Proj.awayι_toSpecZero_assoc,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective (Submonoid.powers (f s.2.1))
  change (HomogeneousLocalization.Away.map f s.2.1
    (HomogeneousLocalization.fromZeroRingHom (grading u v) (Submonoid.powers s.2.1)
      (algebraMap K ((grading u v) 0) a))).val =
      (HomogeneousLocalization.fromZeroRingHom (grading v u) (Submonoid.powers (f s.2.1))
        (algebraMap K ((grading v u) 0) a)).val
  simp only [HomogeneousLocalization.Away.map,HomogeneousLocalization.val_map,
    HomogeneousLocalization.val_fromZeroRingHom,IsLocalization.map_eq,
    SetLike.GradeZero.coe_algebraMap]
  exact congrArg _ ((coordinateHom u v r hr).commutes a)

/-- Scheme isomorphism over the coefficient field, on the proper models. -/
def overIso (u v r : K) (hr : r^2 = -2) :
    Over.mk (projectiveStructure (c v u)) ≅ Over.mk (projectiveStructure (c u v)) :=
  Over.isoMk (projectiveIso u v r hr) (projHom_over u v r hr)

/-- The proper four-quadric model of the twist 2d y² = f(u,v,x). -/
abbrev model (u v d : K) := Over.mk (projectiveStructure (c (u/(2*d)) (v/(2*d))))

omit [CharZero K] in
theorem model_proper (u v d : K) : IsProper (model u v d).hom :=
  proper_projectiveStructure _

theorem finite_chart_equation (u v d x y : K) (hd : d ≠ 0) :
    y^2 = sextic (c (u/(2*d)) (v/(2*d))) x ↔
      2*d*y^2 = PicardConjugation.binarySextic u v x 1 := by
  have he : sextic (c (u/(2*d)) (v/(2*d))) x =
      PicardConjugation.binarySextic u v x 1/(2*d) := by
    simp [sextic,Picard.coefficients,PicardConjugation.binarySextic]
    ring
  rw [he,eq_div_iff (mul_ne_zero (by norm_num) hd),mul_comm (y^2)]

omit [CharZero K] in
/-- The coefficients defining the projective model are precisely those of the
Picard polynomial used in the local reduction theorems. -/
theorem polynomial_coefficients (u v : K) :
    (fun i : Fin 7 => (PicardLocal.sextic u v).coeff i) = c u v := by
  have e : PicardLocal.sextic u v = equationPolynomial (c u v) := by
    simp [PicardLocal.sextic,PicardLocal.quadratic,PicardLocal.quartic,equationPolynomial,
      sextic,Picard.coefficients,map_ofNat]
    ring
  rw [e]
  have coeff (a : Fin 7 → K) (i : Fin 7) : (equationPolynomial a).coeff i = a i := by
    fin_cases i <;> simp [equationPolynomial,sextic,Polynomial.coeff_X_pow,
      Polynomial.coeff_C,Polynomial.coeff_C_mul]
  exact _root_.funext (coeff (c u v))

omit [CharZero K] in
theorem fibre_degree (u v : K) (hv : v ≠ 0) : (PicardLocal.sextic u v).natDegree = 6 := by
  unfold PicardLocal.sextic PicardLocal.quadratic PicardLocal.quartic
  compute_degree!

open ZInQBlueprint.BinaryCover in
/-- The proper scheme is the standard smooth completion of this very
sextic whenever its three discriminant factors are nonzero. -/
def completionIso (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    sexticCompletion (PicardLocal.sextic u v) (fibre_degree u v hv) ≅
      Over.mk (projectiveStructure (c u v)) := by
  have hs := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0)
    hu hv hD
  let e := (completion_is_quadrics (fibre_degree u v hv) hs).exists.choose
  exact e ≪≫ eqToIso (congrArg (fun a : Fin 7 → K => Over.mk (projectiveStructure a))
    (polynomial_coefficients u v))

open PicardConjugation in
/-- All rationally twisted Picard models are isomorphic over the same explicit
finite Galois field to every coefficient conjugate. -/
theorem conjugate_proper_model (σ : fixedField ≃ₐ[ℚ] fixedField) (s d : ℚ) :
    Nonempty (model (U s) (V s) (d:fixedField) ≅
      model (σ (U s)) (σ (V s)) (σ (d:fixedField))) := by
  rw [map_ratCast]
  rcases coefficient_action σ s with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
    exact ⟨Iso.refl _⟩
  · rw [hu,hv]
    exact ⟨overIso _ _ r r_sq⟩

open ZInQ ZInQ.QualitativeHeight PicardConjugation in
private theorem regular_parameters (t : ℚ) (ht : t ∉ contactSet) :
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
private theorem twist_regular (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0) :
    let s := picardParameter t
    let a := U s/(2*(d:fixedField))
    let b := V s/(2*(d:fixedField))
    a ≠ 0 ∧ b ≠ 0 ∧ a-b ≠ 0 := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨hu,hv,hD⟩ := regular_parameters t ht
  have nd : 2*(d:fixedField) ≠ 0 := mul_ne_zero (by norm_num) (Rat.cast_ne_zero.mpr hd)
  have ha : a ≠ 0 := div_ne_zero hu nd
  have hb : b ≠ 0 := div_ne_zero hv nd
  have he : a-b ≠ 0 := by
    change U s/_ - V s/_ ≠ 0
    rw [← sub_div]
    exact div_ne_zero hD nd
  exact ⟨ha,hb,he⟩

open ZInQ ZInQ.QualitativeHeight PicardConjugation ZInQBlueprint.BinaryCover in
/-- For every parameter outside the six contacts and every nonzero rational
twist, the proper model is the smooth completion of the very same polynomial. -/
theorem family_smooth_completion (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0) :
    let s := picardParameter t
    let f := PicardLocal.sextic (U s / (2*(d:fixedField))) (V s / (2*(d:fixedField)))
    ∃ deg : f.natDegree = 6, f.Separable ∧ Nonempty (sexticCompletion f deg ≅ model (U s) (V s) d) := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨ha,hb,he⟩ := twist_regular t d ht hd
  exact ⟨fibre_degree a b hb,PicardLocal.good_fibre_separable (by norm_num) (by norm_num) ha hb he,
    ⟨completionIso a b ha hb he⟩⟩

open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian GoodReductionJacobian
attribute [local instance] filteredCommGrpHasColimitsOfShape

open PicardConjugation in
/-- The full relative Picard-zero fppf group sheaves of the conjugate curves
are isomorphic on all test schemes over the fixed coefficient field. -/
theorem conjugate_picard_zero (σ : fixedField ≃ₐ[ℚ] fixedField) (s d : ℚ) :
    Nonempty (ordinaryRelativePicardZeroGroupSheaf (model (U s) (V s) (d:fixedField)).hom ≅
      ordinaryRelativePicardZeroGroupSheaf
        (model (σ (U s)) (σ (V s)) (σ (d:fixedField))).hom) := by
  obtain ⟨e⟩ := conjugate_proper_model σ s d
  exact ⟨(presheafToSheaf (Scheme.fppfTopology.over (Spec (.of fixedField))) CommGrpCat.{1}).mapIso
    (ZInQBlueprint.IntegralPicard.CurveMap.pullIso e.symm)⟩

open CategoryTheory.Limits ZInQBlueprint.BinaryCover Polynomial in
/-- After extension to any field, the two standard affine charts of a
separable sextic are still integral and meet. -/
theorem geometric_integral_quadrics (f : K[X]) (deg : f.natDegree = 6) (sep : f.Separable) :
    GeometricallyIntegral (projectiveStructure (fun i : Fin 7 => f.coeff i)) := by
  let a : Fin 7 → K := fun i => f.coeff i
  let C := Over.mk (projectiveStructure a)
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) AlgebraicGeometry.IsIntegral :=
    ⟨fun e _ => AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := AlgebraicGeometry.IsIntegral) (R := K) (f := C.hom)).mpr
  intro L _ _
  let h := scalarMap K L
  let π := pullback.fst C.hom h
  let Y (i : Bool) := pullback (chartAsOver a i).left π
  let j (i : Bool) : Y i ⟶ _ := pullback.snd (chartAsOver a i).left π
  have range_j (i : Bool) : Set.range (j i) = π ⁻¹' Set.range (chartAsOver a i).left :=
    Scheme.Pullback.range_snd _ _
  let : Surjective h := ⟨Function.surjective_to_subsingleton _⟩
  have sur : Surjective π := inferInstanceAs (Surjective (pullback.fst C.hom h))
  let (i : Bool) : IsOpenImmersion (chartAsOver a i).left :=
    inferInstanceAs (IsOpenImmersion (chartMap a i))
  let (i : Bool) : IsOpenImmersion (j i) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd (chartAsOver a i).left π))
  apply integral_of_two_charts Y j
  · intro i
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
    have dom : IsDomain (Cover G) := domain_separable_cover gd ggood.2.map
    let e : Y i ≅ (SpecOver (R := L) (Cover G)).left :=
      pullbackRightPullbackFstIso C.hom h (chartAsOver a i).left ≪≫
      pullback.congrHom (chartAsOver a i).w rfl ≪≫
      (Over.forget _).mapIso (affineBaseChange K L g).symm
    let : AlgebraicGeometry.IsIntegral (SpecOver (R := L) (Cover G)).left :=
      (affine_isIntegral_iff _).mpr dom
    exact AlgebraicGeometry.IsIntegral.of_isIso e.inv
  · intro x
    obtain ⟨i,y,hy⟩ := cover_projective a (π x)
    exact ⟨i,(range_j i).ge ⟨y,hy⟩⟩
  · obtain ⟨p,hp,hq⟩ := overlapping_charts a
    obtain ⟨q,hq'⟩ := sur.surj p
    refine ⟨q,(range_j true).ge ?_,(range_j false).ge ?_⟩
    · change π q ∈ Set.range _
      rwa [hq']
    · change π q ∈ Set.range _
      rwa [hq']

open ZInQBlueprint.BinaryCover in
private theorem geometry (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    SmoothOfRelativeDimension 1 (projectiveStructure (c u v)) ∧
      GeometricallyIntegral (projectiveStructure (c u v)) := by
  have deg := fibre_degree u v hv
  have sep := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0)
    hu hv hD
  have geo := geometric_integral_quadrics (PicardLocal.sextic u v) deg sep
  rw [polynomial_coefficients] at geo
  have ⟨hI,_,hs,hdim,_⟩ := sexticCompletion_geometry deg sep
  let M := sexticCompletion (PicardLocal.sextic u v) deg
  let : AlgebraicGeometry.IsIntegral M.left := hI
  let : Smooth M.hom := hs
  have hrel := ZInQBlueprint.SixJacobian.relative_dimension_one M.hom hdim
  let e := completionIso u v hu hv hD
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  refine ⟨?_,geo⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    e.hom.left]
  change SmoothOfRelativeDimension 1 (e.hom.left ≫ (Over.mk (projectiveStructure (c u v))).hom)
  rw [e.hom.w]
  exact hrel

open JacobianVarieties.Picard.Unpointed SchemeTheory.RepresentedGroups

/-- The unpointed Jacobian group scheme of the actual proper sextic. -/
def jacobian (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    ZInQBlueprint.AbelianModel.GroupScheme K := by
  let : IsProper (projectiveStructure (c u v)) := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 (projectiveStructure (c u v)) := (geometry u v hu hv hD).1
  let : GeometricallyIntegral (projectiveStructure (c u v)) := (geometry u v hu hv hD).2
  exact groupScheme K (projectiveStructure (c u v))

theorem jacobian_is_abelian (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    ZInQBlueprint.AbelianModel.IsAbelianScheme (jacobian u v hu hv hD) := by
  let C := projectiveStructure (c u v)
  let : IsProper C := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 C := (geometry u v hu hv hD).1
  let : GeometricallyIntegral C := (geometry u v hu hv hD).2
  exact ⟨JacobianVarieties.Picard.Unpointed.proper K C,
    JacobianVarieties.Picard.Unpointed.smooth K C,
    JacobianVarieties.Picard.Unpointed.geometricallyConnected K C⟩

/-- The explicit global isomorphism identifies the unpointed Jacobians as
commutative group schemes over the coefficient field. -/
def jacobianIso (u v r : K) (hr : r^2 = -2) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    jacobian u v hu hv hD ≅ jacobian v u hv hu (sub_ne_zero.mpr (sub_ne_zero.mp hD).symm) := by
  let hD' := sub_ne_zero.mpr (sub_ne_zero.mp hD).symm
  let C := Over.mk (projectiveStructure (c u v))
  let D := Over.mk (projectiveStructure (c v u))
  let : IsProper C.hom := proper_projectiveStructure _
  let : IsProper D.hom := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 C.hom := (geometry u v hu hv hD).1
  let : SmoothOfRelativeDimension 1 D.hom := (geometry v u hv hu hD').1
  let : GeometricallyIntegral C.hom := (geometry u v hu hv hD).2
  let : GeometricallyIntegral D.hom := (geometry v u hv hu hD').2
  let e : D ≅ C := overIso u v r hr
  let sh := (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of K))) CommGrpCat.{1}).mapIso
    (ZInQBlueprint.IntegralPicard.CurveMap.pullIso e)
  exact (sheafGroupSchemeIso K C.hom).symm ≪≫ SchemeTheory.RepresentedGroups.iso
    (ordinaryRelativePicardZeroGroupSheaf C.hom).obj (ordinaryRelativePicardZeroGroupSheaf D.hom).obj
    (groupSheafRepresentation K C.hom) (groupSheafRepresentation K D.hom)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of K))) CommGrpCat.{1}).mapIso sh) ≪≫
    sheafGroupSchemeIso K D.hom

open ZInQ ZInQ.QualitativeHeight PicardConjugation

/-- The Jacobian of the coefficient-conjugate of a given rationally twisted
smooth fibre, viewed as a group scheme over the fixed number field. -/
def familyJacobian (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (σ : fixedField ≃ₐ[ℚ] fixedField) : ZInQBlueprint.AbelianModel.GroupScheme fixedField := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨ha,hb,he⟩ := twist_regular t d ht hd
  exact jacobian (σ a) (σ b) ((map_ne_zero_iff σ σ.injective).mpr ha)
    ((map_ne_zero_iff σ σ.injective).mpr hb)
    (sub_ne_zero.mpr (σ.injective.ne (sub_ne_zero.mp he)))

/-- Every coefficient conjugate of the actual unpointed Jacobian of each
noncontact fibre and each nonzero rational twist is isomorphic over the
same fixed finite Galois number field, as a commutative group scheme. -/
theorem family_jacobian_conjugate (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (σ : fixedField ≃ₐ[ℚ] fixedField) :
    Nonempty (familyJacobian t d ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField) ≅
      familyJacobian t d ht hd σ) := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨ha,hb,he⟩ := twist_regular t d ht hd
  have e : (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a) := by
    rcases coefficient_action σ s with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · left; simp [a,b,h₁,h₂,map_ofNat]
    · right; simp [a,b,h₁,h₂,map_ofNat]
  have transport {u v u' v' : fixedField} (hu : u≠0) (hv : v≠0) (hD : u-v≠0)
      (hu' : u'≠0) (hv' : v'≠0) (hD' : u'-v'≠0)
      (eqs : (u'=u ∧ v'=v) ∨ (u'=v ∧ v'=u)) :
      Nonempty (jacobian u v hu hv hD ≅ jacobian u' v' hu' hv' hD') := by
    rcases eqs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨Iso.refl _⟩
    · exact ⟨jacobianIso _ _ r r_sq hu hv hD⟩
  exact transport ha hb he ((map_ne_zero_iff σ σ.injective).mpr ha)
    ((map_ne_zero_iff σ σ.injective).mpr hb) (sub_ne_zero.mpr (σ.injective.ne (sub_ne_zero.mp he))) e


open CategoryTheory.Limits ZInQBlueprint.BinaryCover Polynomial in
/-- Scalar extension by a field isomorphism carries the proper sextic model
to the model of the coefficientwise transformed polynomial. The comparison
comes from base change on its specified dense finite chart. -/
def projectiveBaseChange {L : Type} [Field L] [CharZero L] (φ : K ≃+* L)
    (f : K[X]) (deg : f.natDegree = 6) (sep : f.Separable) :
    (Over.pullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
      (Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))) ≅
        Over.mk (projectiveStructure (fun i : Fin 7 => (f.map φ.toRingHom).coeff i)) := by
  let : Algebra K L := φ.toRingHom.toAlgebra
  let g := f.map φ.toRingHom
  have dg : g.natDegree = 6 := (natDegree_map_eq_of_injective φ.injective f).trans deg
  have sg : g.Separable := sep.map
  let X := Over.mk (projectiveStructure (fun i : Fin 7 => f.coeff i))
  let D := Over.mk (projectiveStructure (fun i : Fin 7 => g.coeff i))
  let h := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let B := (Over.pullback h).obj X
  let π : B.left ⟶ X.left := pullback.fst X.hom h
  let : IsIso h := inferInstanceAs (IsIso ((Scheme.Spec.mapIso φ.toCommRingCatIso.op).hom))
  let : IsIso π := inferInstanceAs (IsIso (pullback.fst X.hom h))
  obtain ⟨hX,vX⟩ := projective_regular _ (sextic_charts_dedekind deg sep)
  obtain ⟨hD,vD⟩ := projective_regular _ (sextic_charts_dedekind dg sg)
  let : AlgebraicGeometry.IsIntegral X.left := hX
  let : AlgebraicGeometry.IsIntegral B.left := AlgebraicGeometry.IsIntegral.of_isIso (asIso π).inv
  let : AlgebraicGeometry.IsIntegral D.left := hD
  let : IsProper X.hom := proper_projectiveStructure _
  let : IsProper D.hom := proper_projectiveStructure _
  let : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd X.hom h))
  let A := SpecOver (R := L) (Cover g)
  let : Nonempty A.left := inferInstanceAs (Nonempty (Spec (.of (Cover g))))
  let e : A ≅ (Over.pullback h).obj (SpecOver (R := K) (Cover f)) := affineBaseChange K L f
  let j := (Over.pullback h).map (finiteChartMap deg)
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  let : IsOpenImmersion j.left := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) j.left π]
    have fac : j.left ≫ π = pullback.fst (SpecOver (R := K) (Cover f)).hom h ≫
        (finiteChartMap deg).left := pullback.lift_fst ..
    rw [fac]
    infer_instance
  let i : A ⟶ B := e.hom ≫ j
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ j.left))
  exact (ZInQBlueprint.CurveExtension.unique_model_iso i (finiteChartMap dg)
    (fun p => (open_stalk_prevaluation π p).mp (vX (π p))) vD).exists.choose

set_option maxHeartbeats 1200000 in
open ZInQBlueprint.BinaryCover Polynomial in
private def coefficientBaseChange {L : Type} [Field L] [CharZero L] (φ : K ≃+* L)
    (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    (Over.pullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
      (Over.mk (projectiveStructure (c u v))) ≅ Over.mk (projectiveStructure (c (φ u) (φ v))) := by
  have hs := PicardLocal.good_fibre_separable (by norm_num : (2:K)≠0) (by norm_num : (3:K)≠0)
    hu hv hD
  have e := projectiveBaseChange φ (PicardLocal.sextic u v) (fibre_degree u v hv) hs
  have hm : (PicardLocal.sextic u v).map φ.toRingHom = PicardLocal.sextic (φ u) (φ v) := by
    simp [PicardLocal.sextic,PicardLocal.quadratic,PicardLocal.quartic]
  rw [hm,polynomial_coefficients u v,polynomial_coefficients (φ u) (φ v)] at e
  exact e

/-- Actual base change of the group scheme by a field isomorphism agrees
with the Jacobian of the conjugated coefficients. -/
def jacobianBaseChange {L : Type} [Field L] [CharZero L] (φ : K ≃+* L)
    (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hD : u-v ≠ 0) :
    (ZInQBlueprint.AbelianModel.baseChange φ.toRingHom).obj (jacobian u v hu hv hD) ≅
      jacobian (φ u) (φ v) ((map_ne_zero_iff φ φ.injective).mpr hu) ((map_ne_zero_iff φ φ.injective).mpr hv)
        (sub_ne_zero.mpr (φ.injective.ne (sub_ne_zero.mp hD))) := by
  let : Algebra K L := φ.toRingHom.toAlgebra
  let C := Over.mk (projectiveStructure (c u v))
  let D := Over.mk (projectiveStructure (c (φ u) (φ v)))
  let : IsProper C.hom := proper_projectiveStructure _
  let : IsProper D.hom := proper_projectiveStructure _
  let : SmoothOfRelativeDimension 1 C.hom := (geometry u v hu hv hD).1
  let : GeometricallyIntegral C.hom := (geometry u v hu hv hD).2
  have gd := geometry (φ u) (φ v) ((map_ne_zero_iff φ φ.injective).mpr hu) ((map_ne_zero_iff φ φ.injective).mpr hv)
    (sub_ne_zero.mpr (φ.injective.ne (sub_ne_zero.mp hD)))
  let : SmoothOfRelativeDimension 1 D.hom := gd.1
  let : GeometricallyIntegral D.hom := gd.2
  exact ZInQBlueprint.IntegralPicard.unpointed_baseChangeIso C D (coefficientBaseChange φ u v hu hv hD)

/-- The Jacobian of every noncontact rational fibre and its nonzero rational
twists is isomorphic to its actual Galois pullback over the fixed field. -/
theorem family_galois_pullback (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (σ : fixedField ≃ₐ[ℚ] fixedField) :
    let J := familyJacobian t d ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
    Nonempty ((ZInQBlueprint.AbelianModel.baseChange σ.toRingHom).obj J ≅ J) := by
  let s := picardParameter t
  let a := U s/(2*(d:fixedField))
  let b := V s/(2*(d:fixedField))
  obtain ⟨ha,hb,hD⟩ := twist_regular t d ht hd
  let e := jacobianBaseChange σ.toRingEquiv a b ha hb hD
  let g := Classical.choice (family_jacobian_conjugate t d ht hd σ)
  exact ⟨e ≪≫ g.symm⟩

end
end ZOverQ.Qualitative.PicardDescent

#print axioms ZOverQ.Qualitative.PicardDescent.projectiveIso
#print axioms ZOverQ.Qualitative.PicardDescent.overIso
#print axioms ZOverQ.Qualitative.PicardDescent.model_proper
#print axioms ZOverQ.Qualitative.PicardDescent.finite_chart_equation
#print axioms ZOverQ.Qualitative.PicardDescent.completionIso
#print axioms ZOverQ.Qualitative.PicardDescent.conjugate_proper_model

#print axioms ZOverQ.Qualitative.PicardDescent.family_smooth_completion
#print axioms ZOverQ.Qualitative.PicardDescent.conjugate_picard_zero

#print axioms ZOverQ.Qualitative.PicardDescent.geometric_integral_quadrics
#print axioms ZOverQ.Qualitative.PicardDescent.jacobianIso

#print axioms ZOverQ.Qualitative.PicardDescent.family_jacobian_conjugate

#print axioms ZOverQ.Qualitative.PicardDescent.jacobian_is_abelian

#print axioms ZOverQ.Qualitative.PicardDescent.projectiveBaseChange
#print axioms ZOverQ.Qualitative.PicardDescent.jacobianBaseChange
#print axioms ZOverQ.Qualitative.PicardDescent.family_galois_pullback
