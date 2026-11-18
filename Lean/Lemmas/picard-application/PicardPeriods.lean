import PicardPolynomial

/-! A universal genus-two period comparison on the ordinary polynomial and the
unpointed Jacobian of its smooth projective completion. Streng, §7, Lemma 7.3
(https://doi.org/10.1090/S0025-5718-2013-02712-3), identifies the weighted
forms. Pazuki, Corollary 1.3(1) (https://doi.org/10.24033/bsmf.2623),
bounds the height of the same projective theta coordinates.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open ZInQ ZInQ.QualitativeHeight ZInQBlueprint.AbelianModel ZInQBlueprint.ThetaQuotient
open ZOverQ.Qualitative.Picard ZOverQ.Qualitative.Picard.Theta
open ZOverQ.Qualitative.Picard.Assembly ZOverQ.Qualitative.PicardLocalization
open ZOverQ.Qualitative.PicardConjugation ZOverQ.Qualitative.PicardPolynomial

namespace ZOverQ.Qualitative.PicardPeriods
noncomputable section

variable {M : Type} [Field M] [NumberField M]

/-- The numerical consequences at one common canonical period of a smooth
genus-two sextic. The algebraic projective representative may be defined
over its own number field. Realization of such a period for a given absolute
stable height, including theta algebraicity, is an external input. -/
def SexticPeriods (η : M →+* ℂ) (F : GroupScheme M → ℝ) : Prop :=
  ∀ (f : M[X]) (df : f.natDegree = 6) (sf : f.Separable),
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (ι : N →+* ℂ) (x : Fin 16 → N)
      (Z : SiegelMatrix) (p w : ℂˣ),
      (∀ i, ι (x i) = (p:ℂ) * nulls Z i) ∧
      -120 * secondInvariant (fun i : Fin 7 => (f.map η).coeff i) =
        (w:ℂ) * h12 (nulls Z) / h10 (nulls Z) ∧
      (f.map η).discr = (w:ℂ)^5 * h10 (nulls Z) ∧
      PazukiAt (euclideanHeight x) (F (completionJacobian f df sf))

private theorem primitive_sextic (η : M →+* ℂ) (s : ℚ) (e : ℤ) (q : M) :
    let c := 2*(e:ℂ)*(s.den:ℂ)^6
    (LocalSupport.twisted s.num s.den e q).map η =
      PicardLocal.sextic (c*(((s:ℂ)+η q)^6)) (c*(((s:ℂ)-η q)^6)) := by
  dsimp only
  have hn : (s.num:ℂ) = (s:ℂ)*(s.den:ℂ) := by exact_mod_cast (Rat.mul_den_eq_num s).symm
  have hu : ((s.num:ℂ)+η q*(s.den:ℂ))^6 = (s.den:ℂ)^6*((s:ℂ)+η q)^6 := by rw [hn]; ring
  have hv : ((s.num:ℂ)-η q*(s.den:ℂ))^6 = (s.den:ℂ)^6*((s:ℂ)-η q)^6 := by rw [hn]; ring
  have mapped : (LocalSupport.twisted s.num s.den e q).map η =
      LocalSupport.twisted s.num s.den e (η q) := by
    simp [LocalSupport.twisted,PicardLocal.sextic_map,LocalSupport.upper,LocalSupport.lower,map_ofNat]
  rw [mapped,LocalSupport.twisted]
  simp only [LocalSupport.upper, LocalSupport.lower, Int.cast_natCast, hu, hv]
  rw [← LocalSupport.sextic_scale]
  congr 1 <;> ring

/-- Both ordinary invariants on the primitive polynomial retain the single
weighted multiplier after removing the scalar from its coefficients. -/
private def periods_of_twist {N : Type} [Field N] {s : ℚ} {q : M} {e : ℤ}
    (η : M →+* ℂ) (hq : q^2 = -3) (he : e ≠ 0)
    {x : Fin 16 → N} {ι : N →+* ℂ} (Z : SiegelMatrix) (p w : ℂˣ)
    (coords : ∀ i, ι (x i) = (p:ℂ)*nulls Z i)
    (two : -120 * secondInvariant
      (fun i : Fin 7 => ((LocalSupport.twisted s.num s.den e q).map η).coeff i) =
      (w:ℂ) * h12 (nulls Z) / h10 (nulls Z))
    (ten : ((LocalSupport.twisted s.num s.den e q).map η).discr = (w:ℂ)^5 * h10 (nulls Z)) :
    PeriodForms s x ι := by
  let U := ((s:ℂ)+η q)^6
  let V := ((s:ℂ)-η q)^6
  let c := 2*(e:ℂ)*(s.den:ℂ)^6
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast he))
    (pow_ne_zero _ (by exact_mod_cast s.den_nz))
  have hρ : (η q)^2 = -3 := by rw [← map_pow,hq,map_neg,map_ofNat]
  have hs : (s:ℂ)^2+3 ≠ 0 := by
    have h : (s^2+3 : ℚ) ≠ 0 := by positivity
    exact_mod_cast h
  have hV : V ≠ 0 := right_ne_zero_of_mul ((sixth_product (s:ℂ) _ hρ).trans_ne (pow_ne_zero _ hs))
  have poly : (LocalSupport.twisted s.num s.den e q).map η = PicardLocal.sextic (c*U) (c*V) :=
    primitive_sextic η s e q
  rw [poly, PicardDescent.polynomial_coefficients] at two
  rw [poly, discr_sextic _ _ (mul_ne_zero hc hV)] at ten
  have scale₂ : secondInvariant (coefficients (c*U) (c*V)) = c^2 * secondInvariant (coefficients U V) := by
    rw [secondInvariant_eq,secondInvariant_eq]; ring
  have scale₁₀ : discriminantValue (c*U) (c*V) = c^10*discriminantValue U V := by
    unfold discriminantValue; ring
  change -120 * secondInvariant (coefficients (c*U) (c*V)) = _ at two
  rw [scale₂] at two
  rw [scale₁₀] at ten
  let v : ℂˣ := Units.mk0 c hc
  have eff : ((w/v^2 : ℂˣ):ℂ) = (w:ℂ)/c^2 := by simp [v]
  refine ⟨η q,hρ,nulls Z,p,coords,w/v^2,?_,?_⟩ <;> rw [eff]
  · change -120*secondInvariant (coefficients U V) = ((w:ℂ)/c^2)*h12 (nulls Z)/h10 (nulls Z)
    calc
      _ = ((w:ℂ)*h12 (nulls Z)/h10 (nulls Z))/c^2 := by
        apply (eq_div_iff (pow_ne_zero _ hc)).2
        linear_combination two
      _ = _ := by ring
  · change discriminantValue U V = ((w:ℂ)/c^2)^5*h10 (nulls Z)
    field_simp [hc]
    linear_combination ten

/-- The projective coordinate pair of the rational weight-zero invariant. -/
def invariantLine : InvariantCharts ℚ 2 1 where
  degree := fun _ => 1
  equation := fun _ i => MvPolynomial.X i
  homogeneous := fun _ i => MvPolynomial.isHomogeneous_X ℚ i

theorem invariantLine_point (r : ℚ) :
    invariantLine.Represents ![r,1] r ∧ normalizedHeight ![r,1] = ratHeight r := by
  constructor
  · refine ⟨0,?_,?_⟩ <;> simp [invariantLine]
  · have h := relative_rational_height (K := ℚ) r
    have eqn := Height.logHeight₁_div_eq_logHeight r (1:ℚ)
    rw [div_one] at eqn
    simpa [normalizedHeight,← eqn] using h

omit [NumberField M] in
open scoped CategoryTheory.MonObj CategoryTheory.Obj in
/-- A geometric kernel of an isomorphism has precisely one point. -/
theorem kernelDegree_iso {A B : GroupScheme M} (i : A ≅ B) :
    IsogenyHeight.kernelDegree i.hom = 1 := by
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap M (AlgebraicClosure M))))
  let u := i.hom.hom.hom.hom
  let : IsIso u := inferInstanceAs (IsIso (((CommGrp.forget _).mapIso i).hom))
  let k := {x : T ⟶ A.X // x ≫ u = 1}
  let : Unique k :=
    { default := ⟨1, MonObj.one_comp u⟩
      uniq := fun x => Subtype.ext ((cancel_mono u).mp (x.property.trans (MonObj.one_comp u).symm)) }
  exact Nat.card_unique (α := k)

omit [NumberField M] in
/-- Isomorphism invariance of the stable height follows from the isogeny
inequality and its actual geometric kernel degree. -/
theorem stableHeight_iso (F : GroupScheme M → ℝ) (stable : IsogenyHeight.StableHeight F)
    {A B : GroupScheme M} (a : IsAbelianScheme A) (i : A ≅ B) : F A = F B := by
  let e := (CommGrp.forget _).mapIso i
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  let : IsIso i.hom.hom.hom.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  have eqn : e.inv.left ≫ A.X.hom = B.X.hom := e.inv.w
  have sq : IsPullback e.inv.left B.X.hom A.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨eqn.trans (Category.comp_id _).symm⟩
  have b : IsAbelianScheme B := ⟨MorphismProperty.of_isPullback (P := @IsProper) sq a.proper,
    MorphismProperty.of_isPullback (P := @Smooth) sq a.smooth,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq a.geometricallyConnected⟩
  have h := stable.isogeny a b i.hom ⟨inferInstance,inferInstance⟩
  rw [kernelDegree_iso] at h
  symm
  simpa only [Nat.cast_one,Real.log_one,zero_div,abs_nonpos_iff,sub_eq_zero] using h

/-- The fixed rational chart works for every noncontact twist. The only
period input is uniform in all smooth sextics over M. -/
theorem polarizedModuliHeight_of_periods (ψ : fixedField →ₐ[ℚ] M)
    (η : M →+* ℂ) (F : GroupScheme M → ℝ)
    (stable : IsogenyHeight.StableHeight F)
    (periods : SexticPeriods η F) :
    PolarizedModuliHeight invariantLine ψ F ∅ 84 289200 := by
  intro t ht _
  let s := picardParameter t
  let e : ℤ := PrimitiveTwist.twist s
  have he : e ≠ 0 := by dsimp [e]; exact_mod_cast (PrimitiveTwist.positive s).ne'
  let q := ψ ρ
  have hq : q^2 = -3 := by dsimp [q]; rw [← map_pow,rho_sq,map_neg,map_ofNat]
  let f := LocalSupport.twisted s.num s.den e q
  obtain ⟨df,sf,⟨ident⟩⟩ := family_primitive_jacobian ψ.toRingHom t e ht he
  let J := (baseChange ψ.toRingHom).obj (twistedJacobian t ht)
  have equ : J ≅ completionJacobian f df sf := ident
  obtain ⟨N,instField,instNumber,ι,x,Z,p,w,coords,two,ten,hp⟩ := periods f df sf
  have forms := periods_of_twist η hq he Z p w coords two ten
  have hJ : F J = F (completionJacobian f df sf) :=
    stableHeight_iso F stable (isAbelianScheme_baseChange _ (twistedJacobian_abelian t ht)) equ
  rw [←hJ] at hp
  have bound := invariant_of_isogeny (primitiveBranch_ne_zero ht) forms (r := 1) (D := 1)
    (B := F J) (by decide) (by decide) hp (by simp)
  let r := igusaRatio (chart s)
  obtain ⟨rep,height⟩ := invariantLine_point r
  refine ⟨![r,1],rep,?_⟩
  rw [height]
  simpa [r,s,J] using bound

/-- The single family input left by the universal genus-two period comparison is
the rational quaternionic isogeny over a fixed number field. -/
theorem integer_polynomial_of_sextic_periods
    (M : Type) [Field M] [NumberField M] [Normal ℚ M] (ψ : fixedField →ₐ[ℚ] M) (η : M →+* ℂ)
    (hF : GroupScheme ℚ → ℝ) (F : GroupScheme M → ℝ)
    (vk : VonKanel hF) (criterion : PicardGoodReduction.SplitSexticDDMM)
    (st : ∀ (p : ℕ) [Fact p.Prime], SerreTateAt p)
    (D : ℕ) (stable : IsogenyHeight.StableHeight F) (degree : IsogenyHeight.DegreeBound F (2*D))
    (extend : ∀ B : GroupScheme ℚ, IsAbelianScheme B → F ((baseChange (algebraMap ℚ M)).obj B) = hF B)
    (except : Finset ℚ) (descent : MarkedIsogenies ψ D except) (periods : SexticPeriods η F)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial :=
  integer_polynomial_of_picard_jacobians invariantLine M ψ hF F vk criterion st D stable degree
    extend except ∅ 84 289200 (by norm_num) descent (polarizedModuliHeight_of_periods ψ η F stable periods)
    tian grossZagier

end
end ZOverQ.Qualitative.PicardPeriods

#print axioms ZOverQ.Qualitative.PicardPeriods.kernelDegree_iso
#print axioms ZOverQ.Qualitative.PicardPeriods.stableHeight_iso
#print axioms ZOverQ.Qualitative.PicardPeriods.invariantLine_point
#print axioms ZOverQ.Qualitative.PicardPeriods.polarizedModuliHeight_of_periods
#print axioms ZOverQ.Qualitative.PicardPeriods.integer_polynomial_of_sextic_periods
