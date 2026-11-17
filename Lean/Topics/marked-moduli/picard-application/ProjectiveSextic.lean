import QuadricsGeometry
/-! The four-quadric model of the paper curve and of the specified DDMM polynomial. -/
open CategoryTheory AlgebraicGeometry Polynomial ZInQBlueprint.BinaryCover
open ZInQBlueprint.IntegralSextic ZInQBlueprint.ResidualFactors ZInQBlueprint.GlobalTwist
open ZInQBlueprint.CurveChart ZInQBlueprint.DirectCharts
namespace ZInQBlueprint.SexticEmbedding
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K]

/-- Polynomial automorphisms of the affine line preserve degree. -/
theorem natDegree_algEquiv (e : K[X] ≃ₐ[K] K[X]) (p : K[X]) : (e p).natDegree = p.natDegree := by
  have act (f : K[X] ≃ₐ[K] K[X]) (a : K[X]) : f a = a.comp (f X) := by
    let g : K[X] →ₐ[K] K[X] := Polynomial.aeval (f X)
    have eq : f.toAlgHom = g := by
      apply Polynomial.algHom_ext
      simp [g]
    exact (DFunLike.congr_fun eq a).trans (aeval_def _ _)
  have eq : (e.symm X).natDegree * (e X).natDegree = 1 := by
    rw [← natDegree_comp, ← act, e.apply_symm_apply, natDegree_X]
  have he : (e X).natDegree = 1 := Nat.eq_one_of_dvd_one ⟨_,by rw [mul_comm]; exact eq.symm⟩
  rw [act,natDegree_comp,he,mul_one]

private theorem coeff_reverse_six {f : K[X]} (hd : f.natDegree = 6) :
    (fun i : Fin 7 => f.reverse.coeff i) = fun i => f.coeff i.rev := by
  funext i
  have hi : (i:ℕ) ≤ 6 := by omega
  rw [coeff_reverse,hd,revAt_le hi,Fin.val_rev]
  congr 1
  omega

/-- Both coordinate rings recover the indicated (finite or reversed) sextic. -/
theorem polynomial_chart {f : K[X]} (hd : f.natDegree = 6) (b : Bool) :
    equationPolynomial (coefficients (fun i => f.coeff i) b) = if b then f.reverse else f := by
  cases b
  · exact coefficient_equation f hd.le
  · change equationPolynomial (fun i : Fin 7 => f.coeff i.rev) = f.reverse
    rw [← coeff_reverse_six hd]
    exact coefficient_equation _ (f.reverse_natDegree_le.trans hd.le)

variable [CharZero K]
/-- A degree-six separable polynomial has Dedekind coordinate rings on both standard projective opens. -/
theorem sextic_charts_dedekind {f : K[X]} (hd : f.natDegree = 6) (hs : f.Separable) (b : Bool) :
    IsDedekindDomain (SquareChart (fun i => f.coeff i) b) := by
  let : Invertible (2:K) := invertibleOfNonzero (by norm_num)
  unfold SquareChart
  rw [polynomial_chart hd]
  cases b
  · exact dedekind_cover (by change 0 < f.natDegree; omega) hs
  · obtain ⟨⟨h,_⟩,s⟩ := reverse_sextic_regular hd hs
    exact dedekind_cover (by change 0 < f.reverse.natDegree; omega) s

/-- The projective finite chart, using the exact polynomial rather than a coefficient presentation. -/
def finiteChartMap {f : K[X]} (hd : f.natDegree = 6) :
    SpecOver (R := K) (Cover f) ⟶ Over.mk (projectiveStructure (fun i => f.coeff i)) :=
  eqToHom (congrArg (fun g : K[X] => SpecOver (R := K) (Cover g)) (polynomial_chart hd false).symm) ≫
    chartAsOver _ false

instance {f : K[X]} (hd : f.natDegree = 6) : IsOpenImmersion (finiteChartMap hd).left := by
  unfold finiteChartMap
  change IsOpenImmersion (_ ≫ chartMap _ false)
  infer_instance

/-- Unique isomorphism over K, fixing the finite chart, from the smooth two-chart completion
to the closed four-quadric subscheme of projective four-space. -/
theorem completion_is_quadrics {f : K[X]} (hd : f.natDegree = 6) (hs : f.Separable) :
    ∃! e : sexticCompletion f hd ≅ Over.mk (projectiveStructure (fun i => f.coeff i)),
      chartInclusion K f f.reverse (reverse_sextic_overlap hd) false ≫ e.hom = finiteChartMap hd := by
  obtain ⟨hI,hP,_,_,hV⟩ := sexticCompletion_geometry hd hs
  obtain ⟨qI,qV⟩ := projective_regular _ (sextic_charts_dedekind hd hs)
  let : AlgebraicGeometry.IsIntegral (sexticCompletion f hd).left := hI
  let : IsProper (sexticCompletion f hd).hom := hP
  let : Nonempty (SpecOver (R := K) (Cover f)).left :=
    inferInstanceAs (Nonempty (Spec (.of (Cover f))))
  let : AlgebraicGeometry.IsIntegral (Over.mk (projectiveStructure (fun i => f.coeff i))).left := qI
  let : IsProper (Over.mk (projectiveStructure (fun i => f.coeff i))).hom := proper_projectiveStructure _
  let : IsOpenImmersion (chartInclusion K f f.reverse (reverse_sextic_overlap hd) false).left :=
    chartInclusion_open ..
  exact ZInQBlueprint.CurveExtension.unique_model_iso (U := SpecOver (R := K) (Cover f)) _ _ hV qV

theorem paper_degree_six {u : ℚ} (hu : u ∉ ZInQ.contactSet) (b : Bool) : (paper K u b).natDegree = 6 := by
  obtain ⟨s,t,e,hs,_,he⟩ := chart_normal_form hu b
  rw [← paper_baseChange, natDegree_map_eq_of_injective (algebraMap ℚ K).injective, ← he,
      natDegree_algEquiv, natDegree_C_mul hs, (monic_six t).2]

theorem paper_is_quadrics {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    let f := paper K u false
    ∃! e : paperModel K u ≅ Over.mk (projectiveStructure (fun i => f.coeff i)),
      chartInclusion K _ _ (paper_overlap K u) false ≫ e.hom = finiteChartMap (paper_degree_six hu false) := by
  let f := paper K u false
  have hd : f.natDegree = 6 := paper_degree_six hu false
  have hs : f.Separable := (paper_chart_regular K hu false).2
  obtain ⟨qI,qV⟩ := projective_regular _ (sextic_charts_dedekind hd hs)
  let : AlgebraicGeometry.IsIntegral (paperModel K u).left := paper_reglued_integral K hu
  let : IsProper (paperModel K u).hom := paper_proper K u
  let : Nonempty (SpecOver (R := K) (Cover f)).left :=
    inferInstanceAs (Nonempty (Spec (.of (Cover f))))
  let : AlgebraicGeometry.IsIntegral (Over.mk (projectiveStructure (fun i => f.coeff i))).left := qI
  let : IsProper (Over.mk (projectiveStructure (fun i => f.coeff i))).hom := proper_projectiveStructure _
  let : IsOpenImmersion (chartInclusion K _ _ (paper_overlap K u) false).left := chartInclusion_open ..
  exact ZInQBlueprint.CurveExtension.unique_model_iso (U := SpecOver (R := K) (Cover f)) _ _ (paper_prevaluation K hu) qV

end
end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.natDegree_algEquiv
#print axioms ZInQBlueprint.SexticEmbedding.completion_is_quadrics
#print axioms ZInQBlueprint.SexticEmbedding.paper_degree_six
#print axioms ZInQBlueprint.SexticEmbedding.paper_is_quadrics
