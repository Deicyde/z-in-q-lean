import DDMMPolynomial
import ProperCompletion
import SmoothSextic
import CurveDimension

/-! A complete smooth model of the actual local polynomial by the two standard charts. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable {K : Type} [Field K] [CharZero K]

private abbrev chartPair (f : K[X]) : Bool → K[X] := fun i => if i then f.reverse else f

/-- The usual smooth proper completion of y²=f(x), obtained by adjoining
the affine chart w²=z⁶ f(1/z) at infinity. -/
def sexticCompletion (f : K[X]) (hd : f.natDegree = 6) : Over (Spec (.of K)) :=
  gluedOver K f f.reverse (reverse_sextic_overlap hd)

private theorem completion_regular {f : K[X]} (hd : f.natDegree = 6) (hs : f.Separable) (i : Bool) :
    0 < (chartPair f i).natDegree ∧ (chartPair f i).Separable := by
  cases i
  · exact ⟨by change 0 < f.natDegree; omega,hs⟩
  · obtain ⟨⟨h,_⟩,s⟩ := reverse_sextic_regular hd hs
    exact ⟨by change 0 < f.reverse.natDegree; omega,s⟩

/-- This completion is integral, proper, smooth of dimension one, and has valuation stalks. -/
theorem sexticCompletion_geometry {f : K[X]} (hd : f.natDegree = 6) (hs : f.Separable) :
    let D := sexticCompletion f hd
    AlgebraicGeometry.IsIntegral D.left ∧ IsProper D.hom ∧ Smooth D.hom ∧
    topologicalKrullDim D.left = 1 ∧ ∀ z : D.left, PreValuationRing (D.left.presheaf.stalk z) := by
  let P := chartPair f
  let h : SexticOverlap K (P false) (P true) := reverse_sextic_overlap hd
  let : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have reg := completion_regular hd hs
  have sm (i : Bool) : Smooth (SpecOver (R := K) (Cover (P i))).hom :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr (smooth_cover _ (reg i).2))
  have hp : IsProper (gluedOver K _ _ h).hom := by
    rw [← curve_structure]
    let : IsFinite (toLine K (P false) (P true) h) := finite_toLine K _ _ h
    let : IsProper (lineStructure K) := line_proper K
    exact IsProper.stableUnderComposition.comp_mem _ _ (inferInstanceAs (IsProper (toLine K _ _ h))) (line_proper K)
  exact ⟨integral_glued_of_domains K P h (fun i => domain_separable_cover (reg i).1 (reg i).2),
    hp,smooth_glued _ _ h (sm false) (sm true),dimension_glued K _ _ h,
    prevaluation_glued_of_dedekind K P h (fun i => dedekind_cover (reg i).1 (reg i).2)⟩

/-- The literal Q_p base change of the rational paper curve is uniquely isomorphic,
over the specified affine equation, to its explicit smooth proper reciprocal-chart completion.
The input arithmetic data are exactly the chart coordinates and unmarked parameter. -/
theorem ddmm_smooth_completion_iso {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    let f := GoodReductionCharts.polynomial p u v a t
    let hd := (ddmm_sextic_regular hu v a t hc).1
    let D := sexticCompletion f hd
    ∃ j : SpecOver (R := ℚ_[p]) (Cover f) ⟶ paperPullback ℚ_[p] u, IsOpenImmersion j.left ∧
      ∃! e : paperPullback ℚ_[p] u ≅ D, j ≫ e.hom = chartInclusion ℚ_[p] f f.reverse (reverse_sextic_overlap hd) false := by
  let f := GoodReductionCharts.polynomial p u v a t
  obtain ⟨j,hj,uniq⟩ := unique_ddmm_completion hu v a t hc
  have ⟨hd,hs⟩ := ddmm_sextic_regular hu v a t hc
  let D := sexticCompletion f hd
  obtain ⟨hi,hp,_,_,hval⟩ := sexticCompletion_geometry hd hs
  let : AlgebraicGeometry.IsIntegral D.left := hi
  let : IsProper D.hom := hp
  let k : SpecOver (R := ℚ_[p]) (Cover f) ⟶ D := chartInclusion ℚ_[p] f f.reverse (reverse_sextic_overlap hd) false
  let hk : IsOpenImmersion k.left := chartInclusion_open ..
  exact ⟨j,hj,@uniq D hp hi k hk hval⟩

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.sexticCompletion_geometry
#print axioms ZInQBlueprint.BinaryCover.ddmm_smooth_completion_iso
