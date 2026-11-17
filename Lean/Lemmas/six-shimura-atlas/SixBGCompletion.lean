import SixModularSextic
import PrintedJacobian

/-! The normalized Corollary 3.15 sextic and its actual affine chart in
the smooth proper curve used in the marking theorem. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover PrintedModel SexticEmbedding NormalDescent
noncomputable section
set_option maxHeartbeats 2000000
variable {K : Type} [Field K] [CharZero K]

/-- A genuine affine-line automorphism carries the printed branch divisor to
the normalized modular divisor with the stated ordinate factor. -/
theorem period_polynomial {s k : K} (hk : k^2 = 9*s^2-32) (hn : k ≠ 0) :
    dilate (Units.mk0 (-k) (neg_ne_zero.mpr hn)) (SexticCalibration.sextic (-s)) =
      C (-4*k^6) * modularPolynomial s k := by
  let F := dilate (Units.mk0 (-k) (neg_ne_zero.mpr hn))
  apply Polynomial.funext
  intro x
  have eq : (evalRingHom x).comp F.toRingHom = evalRingHom (-k*x) := by
    apply Polynomial.ringHom_ext
    · intro a
      change (F (C a)).eval x = _
      rw [show F (C a) = C a from F.commutes a]
      simp
    · change (F X).eval x = _
      simp [F]
  have h := DFunLike.congr_fun eq (SexticCalibration.sextic (-s))
  change (F (SexticCalibration.sextic (-s))).eval x =
    (C (-4*k^6) * modularPolynomial s k).eval x
  rw [show (F (SexticCalibration.sextic (-s))).eval x =
      (SexticCalibration.sextic (-s)).eval (-k*x) from h,
      ← SexticConjugation.affine,eval_mul,eval_C,eval_modular]
  exact period_binary s k x 1 hk

theorem modular_regular {u : ℚ} (hu : u ∉ ZInQ.contactSet) {d s k : K}
    (hd : d^2=6) (hs : argument u d = -s) (hk : k^2=9*s^2-32) (hn : k≠0) :
    (modularPolynomial s k).natDegree = 6 ∧ (modularPolynomial s k).Separable := by
  let F := dilate (Units.mk0 (-k) (neg_ne_zero.mpr hn))
  have same : F (SexticCalibration.sextic (argument u d)) =
      C (-4*k^6) * modularPolynomial s k := hs ▸ period_polynomial hk hn
  have unit : (-4*k^6 : K) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hn)
  have hdeg := congrArg natDegree same
  rw [natDegree_algEquiv,natDegree_C_mul unit,printed_degree hu hd] at hdeg
  have sep := (regular_image F (by rw [printed_degree hu hd]; decide) (printed_separable hu hd)).2
  rw [same] at sep
  exact ⟨hdeg.symm,(associated_unit_mul_left _ (C (-4*k^6)) (isUnit_C.mpr unit.isUnit)).separable sep⟩

/-- The abscissa multiplier is −k and the ordinate multiplier is any
square root of −4k⁶. One dense chart specifies the proper comparison. -/
def modularChartIso {u : ℚ} {d s k v : K} (hs : argument u d = -s)
    (hk : k^2=9*s^2-32) (hn : k≠0) (hv : v^2 = -4*k^6) :
    SpecOver (R := K) (Cover (modularPolynomial s k)) ≅
      SpecOver (R := K) (Cover (SexticCalibration.sextic (argument u d))) := by
  have : v ≠ 0 := by intro eq; rw [eq,zero_pow (by decide : 2≠0)] at hv; exact (mul_ne_zero (by norm_num) (pow_ne_zero _ hn)) hv.symm
  let v' := Units.mk0 v this
  apply specIso (squareEquiv (dilate (Units.mk0 (-k) (neg_ne_zero.mpr hn))) (Units.map C.toMonoidHom v') ?_)
  change _ = C v ^2 * _
  rw [←map_pow,hv,hs]
  exact period_polynomial hk hn

theorem modular_completion {u : ℚ} (hu : u ∉ ZInQ.contactSet) {d s k v : K}
    (hd : d^2=6) (hs : argument u d = -s) (hk : k^2=9*s^2-32) (hn : k≠0)
    (hv : v^2 = -4*k^6) :
    let hd' := (modular_regular hu hd hs hk hn).1
    let P := modularPolynomial s k
    let i := chartInclusion K P P.reverse (reverse_sextic_overlap hd') false
    let j := (modularChartIso hs hk hn hv).hom ≫
      chartInclusion K _ _ (reverse_sextic_overlap (printed_degree hu hd)) false
    ∃! e : sexticCompletion P hd' ≅ PrintedModel.model hu hd, i ≫ e.hom = j := by
  dsimp only
  obtain ⟨deg,sep⟩ := modular_regular hu hd hs hk hn
  obtain ⟨intA,prA,_,_,valA⟩ := sexticCompletion_geometry deg sep
  obtain ⟨intB,prB,_,_,valB⟩ := sexticCompletion_geometry (printed_degree hu hd) (printed_separable hu hd)
  let A := sexticCompletion (modularPolynomial s k) deg
  let B := PrintedModel.model hu hd
  let : AlgebraicGeometry.IsIntegral A.left := intA
  let : IsProper A.hom := prA
  let : AlgebraicGeometry.IsIntegral B.left := intB
  let : IsProper B.hom := prB
  let U := SpecOver (R := K) (Cover (modularPolynomial s k))
  let : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum (Cover (modularPolynomial s k))))
  let l := modularChartIso hs hk hn hv
  let i : U ⟶ A := chartInclusion K _ _ (reverse_sextic_overlap deg) false
  let j' := chartInclusion K _ _ (reverse_sextic_overlap (printed_degree hu hd)) false
  let : IsOpenImmersion i.left := chartInclusion_open ..
  let : IsIso l.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso l).hom))
  let j : U ⟶ B := l.hom ≫ j'
  let oj : IsOpenImmersion j.left := @IsOpenImmersion.comp _ _ _ _ _
    (IsOpenImmersion.of_isIso l.hom.left) (chartInclusion_open ..)
  exact CurveExtension.unique_model_iso (U := U) (X := A) (Y := B) i j valA valB

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.period_polynomial
#print axioms ZInQBlueprint.ShimuraAtlas.modular_regular
#print axioms ZInQBlueprint.ShimuraAtlas.modularChartIso
#print axioms ZInQBlueprint.ShimuraAtlas.modular_completion
