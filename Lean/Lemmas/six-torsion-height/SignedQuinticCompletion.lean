import OddBranchRoots
import SixFixedPoints
import DDMMCompletion

/-! A smooth proper curve over the field of one rational branch point. On
its reciprocal affine chart the polynomial is the specified monic quintic. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.TorsionHeight
open BinaryCover WeightedCurvePoints
noncomputable section
variable {K : Type} [Field K] [CharZero K]

def reciprocalSextic (f : K[X]) (a : K) : K[X] :=
  let g := taylor a f
  let c := f.derivative.eval a
  X + C (g.coeff 2) * X^2 + C (c * g.coeff 3) * X^3 +
    C (c^2 * g.coeff 4) * X^4 + C (c^3 * g.coeff 5) * X^5 + C (c^4 * g.coeff 6) * X^6

omit [CharZero K] in
theorem reciprocal_degree {f : K[X]} {a : K} (hd : f.natDegree = 6)
    (hc : f.derivative.eval a ≠ 0) : (reciprocalSextic f a).natDegree = 6 := by
  have hn : f ≠ 0 := fun h => by simp [h] at hd
  apply le_antisymm
  · dsimp only [reciprocalSextic]
    compute_degree
  · apply le_natDegree_of_ne_zero
    have h6 : ((taylor a) f).coeff 6 = f.leadingCoeff := hd ▸ coeff_taylor_natDegree a f
    simp only [reciprocalSextic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X, h6]
    norm_num [hc,leadingCoeff_ne_zero.mpr hn]

omit [CharZero K] in
theorem reciprocal_reverse {f : K[X]} {a : K} (hd : f.natDegree = 6)
    (hc : f.derivative.eval a ≠ 0) : (reciprocalSextic f a).reverse = oddPolynomial f a := by
  have h := reciprocal_degree hd hc
  have hn := (oddPolynomial_monic_degree f a).2
  ext n
  by_cases hl : 6 < n
  · rw [coeff_eq_zero_of_natDegree_lt (((reverse_natDegree_le _).trans_eq h).trans_lt hl),
      coeff_eq_zero_of_natDegree_lt (by omega : (oddPolynomial f a).natDegree < n)]
  · have : n ≤ 6 := by omega
    rw [coeff_reverse,h,revAt_le this]
    interval_cases n <;> simp only [reciprocalSextic,oddPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C, coeff_mul_X] <;> norm_num

def branchChange (a : K) (c : Kˣ) : K[X] ≃ₐ[K] K[X] :=
  (algEquivAevalXAddC a).trans (dilate c)

theorem chart_equation {f : K[X]} {a : K} (hd : f.natDegree = 6)
    (ha : f.IsRoot a) (hc : f.derivative.eval a ≠ 0) :
    branchChange a (Units.mk0 _ hc) f = C (f.derivative.eval a)^2 * reciprocalSextic f a := by
  let c := f.derivative.eval a
  let e := branchChange a (Units.mk0 c hc)
  apply Polynomial.funext
  intro x
  have map_eval : (evalRingHom x).comp e.toRingHom = evalRingHom (a+c*x) := by
    apply Polynomial.ringHom_ext
    · intro b
      change (e (C b)).eval x = (C b).eval (a+c*x)
      rw [show e (C b) = C b from e.commutes b]
      simp
    · change (e X).eval x = _
      simp [e,branchChange,AlgEquiv.trans_apply,c]; ring
  have eq := DFunLike.congr_fun map_eval f
  change (e f).eval x = f.eval (a+c*x) at eq
  rw [eq,←taylor_eval_sub a f (a+c*x)]
  have bound : (taylor a f).natDegree < 7 := by rw [natDegree_taylor,hd]; decide
  rw [eval_eq_sum_range' bound]
  simp [reciprocalSextic,Finset.sum_range_succ,ha.eq_zero,c]
  ring

/-- The literal base-changed curve is canonically the smooth completion of
the sextic chart above. The other chart is the monic quintic. -/
theorem signed_quintic_completion {u : ℚ} (hu : u ∉ ZInQ.contactSet) {a : K}
    (ha : (paper K u false).IsRoot a) :
    let f := paper K u false
    ∃ (deg : (reciprocalSextic f a).natDegree = 6),
      (reciprocalSextic f a).reverse = oddPolynomial f a ∧
      ∃ j : SpecOver (R := K) (Cover (reciprocalSextic f a)) ⟶ paperPullback K u,
        IsOpenImmersion j.left ∧
        ∃! e : sexticCompletion (reciprocalSextic f a) deg ≅ paperPullback K u,
          chartInclusion K _ _ (reverse_sextic_overlap deg) false ≫ e.hom = j := by
  let f := paper K u false
  let g := reciprocalSextic f a
  have hd : f.natDegree = 6 := finite_degree K hu
  obtain ⟨pos,sep⟩ := paper_chart_regular K hu false
  have hc : f.derivative.eval a ≠ 0 := by
    simpa only [eval₂_id] using sep.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa only [eval₂_id] using ha.eq_zero)
  let v : Kˣ := Units.mk0 _ hc
  let E := branchChange a v
  have he : E f = C (v:K)^2 * g := chart_equation hd ha hc
  let iso := specIso (squareEquiv E (Units.map C.toMonoidHom v) (by
    change E f = (C (v:K))^2 * g
    exact he))
  have deg : g.natDegree = 6 := reciprocal_degree hd hc
  have sep' := (regular_image E pos sep).2
  rw [he] at sep'
  have sg : g.Separable :=
    (associated_unit_mul_left g ((C (v:K))^2) ((isUnit_C.mpr v.isUnit).pow 2)).separable sep'
  obtain ⟨hI,hP,_,_,hV⟩ := sexticCompletion_geometry deg sg
  let D := sexticCompletion g deg
  let : AlgebraicGeometry.IsIntegral D.left := hI
  let : IsProper D.hom := hP
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : IsProper (paperPullback K u).hom := inferInstanceAs
    (IsProper (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ K)))
  let : AlgebraicGeometry.IsIntegral (paperPullback K u).left := integral_baseChange K hu
  let U := SpecOver (R := K) (Cover g)
  let : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum (Cover g)))
  let i : U ⟶ D := chartInclusion K _ _ (reverse_sextic_overlap deg) false
  let j := iso.hom ≫ baseChangedFiniteChart K u
  let : IsOpenImmersion i.left := chartInclusion_open ..
  let : IsIso iso.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso iso).hom))
  let oj : IsOpenImmersion j.left := @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _)
    (inferInstanceAs (IsOpenImmersion (baseChangedFiniteChart K u).left))
  exact ⟨deg,reciprocal_reverse hd hc,j,oj,CurveExtension.unique_model_iso (U := U) i j hV (baseChange_prevaluation K hu)⟩
end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.reciprocal_degree
#print axioms ZInQBlueprint.TorsionHeight.reciprocal_reverse
#print axioms ZInQBlueprint.TorsionHeight.chart_equation
#print axioms ZInQBlueprint.TorsionHeight.signed_quintic_completion

