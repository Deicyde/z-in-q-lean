import RationalOdd
import ThreeScales
import ScalarHeight

/-! The ordinary and scalar tests evaluated directly on the nine decoded elliptic points. -/
namespace Sun28.Forward
open ZInQ Sun28.WitnessIndices Sun28.Ordinary Sun28.Scalar Sun28.ScalarHeight
open NumberField IsDedekindDomain Height
open scoped NumberField
noncomputable section

/-- The involution sending √2 to −√2. -/
def conjugation : K0 ≃ₐ[ℚ] K0 := (starRingAut : K0 ≃+* K0).toRatAlgEquiv

theorem conjugation_nontrivial : conjugation ≠ 1 := by
  intro h
  have e := DFunLike.congr_fun h sqrt2
  change star sqrt2=sqrt2 at e
  rw [K0.star_eq'] at e
  have s := congrArg QuadraticAlgebra.im e
  norm_num [sqrt2] at s


/-- Degree-64 elliptic logarithm evaluated at the actual point. -/
def truncAt (Q : CPoint) : K0 :=
  logTrunc (shortDifferential (-(3-sqrt2)^2)) 64 (parameter (scalarEquiv Q))

def pointRatio (U H : CPoint) : K0 := truncAt U/truncAt H

theorem multiple_ratio (m h : ℤ) :
    ordinaryRatio (paperGenerator sqrt2_sq) m h = pointRatio (m • P) (h • P) := by
  unfold ordinaryRatio pointRatio truncAt
  rw [scalar_index,scalar_index]

/-- All sixteen entries including zero numerators and both conjugations. -/
def ordinaryAt (w : NinePoints) (M : ℕ) (c : ℤ) (β : ℚ) : OrdinaryTest → K0 :=
  let L := fun i => pointRatio (w.U i) w.H
  let V := translated w M c
  let V₀ := translatedBase w c
  let L' := fun i => conjugation (pointRatio (V i) V₀)
  fun i => match i with
  | .h => reciprocal (scalarEquiv w.H)
  | .u j => reciprocal (scalarEquiv (w.U j))
  | .v₀ => conjugation (reciprocal (scalarEquiv V₀))
  | .v j => conjugation (reciprocal (scalarEquiv (V j)))
  | .difference j => L j-L' j
  | .delta => lucas (L 1) (L 2) (L 3)
  | .beta => L 0-algebraMap ℚ K0 β

theorem ordinaryAt_eq {w M c a} (e : Consequences w M c a) (β : ℚ) :
    ordinaryTests sqrt2_sq conjugation c a.h a.n a.m β = ordinaryAt w M c β := by
  funext i
  cases i <;>
    simp only [ordinaryTests,ordinaryAt,multiple_ratio,←scalar_index,e.represented.h_point,
      e.represented.aux_point,e.base_point,e.translated_point]

/-- The nonzero ordinary trace and the two-parameter pole predicate at one scale. -/
def ordinaryAccepted (w : NinePoints) (M : ℕ) (c : ℤ) (β A t : ℚ) (U : Finset ℚ) : Prop :=
  let r := detector A t
  let trace := ordinaryTrace r (fun i => ordinaryAt w M c β i /
    (algebraMap ℚ K0 (t-3))^(orderRequired i+1)) orderRequired
  trace≠0 ∧ polePredicate U (r/trace^2)

theorem ordinaryAccepted_iff {w M c a} (e : Consequences w M c a) (β A t : ℚ) (U : Finset ℚ) :
    ordinaryAccepted w M c β A t U ↔ testTrace sqrt2_sq conjugation c a.h a.n a.m β A t≠0 ∧
      polePredicate U (poleArgument sqrt2_sq conjugation c a.h a.n a.m β A t) := by
  unfold ordinaryAccepted poleArgument testTrace
  rw [ordinaryAt_eq e]

/-- Product of the four actual abscissae. Its two components determine the three scales. -/
def rootProduct (w : NinePoints) (M : ℕ) : K0 := ∏ i, curveX (rootPoints w M i)

theorem rootProduct_eq {w M a} (e : Represents w M a) :
    coordinateProduct a.n = rootProduct w M := by
  unfold coordinateProduct rootProduct
  apply Finset.prod_congr rfl
  intro i _
  change curveX (a.n i • P) = curveX (rootPoints w M i)
  rw [e.root_point]

/-- The six rational entries of Sun's scalar tree. -/
def scalarEntries (w : NinePoints) (M : ℕ) : Fin 6 → ℚ :=
  let H := scalarEquiv w.H
  let R := scalarEquiv (scalarPoint w M)
  let z := parameter R/parameter H
  ![(reciprocal H).re,(reciprocal H).im,(reciprocal R).re,(reciprocal R).im,z.re,z.im]

private theorem basis_components (x : K0) : x = ScalarHeight.pair sqrt2 x.re x.im := by
  unfold ScalarHeight.pair
  rw [mul_comm]
  exact K0.eq_re_add_im_mul_sqrt2 x

theorem components_at {w M c a} (e : Consequences w M c a) :
    Components sqrt2_sq a.h (a.n 1) (scalarEntries w M) := by
  have H : a.h • paperGenerator sqrt2_sq = scalarEquiv w.H := (scalar_index a.h).symm.trans (congrArg _ e.represented.h_point)
  have R : (a.n 1-1) • paperGenerator sqrt2_sq = scalarEquiv (scalarPoint w M) :=
    (scalar_index _).symm.trans (congrArg _ e.scalar_point)
  constructor
  · rw [H]; exact basis_components _
  · rw [R]; exact basis_components _
  · rw [H,R]; exact basis_components _

def scalarAccepted (w : NinePoints) (M : ℕ) (r Γ : ℚ) (D : ℕ) (U : Finset ℚ) : Prop :=
  let deterministic := scalarTree r (scalarEntries w M)
  ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ deterministic≠0 ∧ polePredicate U (signedValue r δ Γ D deterministic)

theorem tree_of_points {w M c a} (e : Consequences w M c a) (r Γ : ℚ) (D : ℕ) (U : Finset ℚ)
    (accepted : scalarAccepted w M r Γ D U) : TreeCertificate sqrt2_sq a.h (a.n 1) r Γ D U := by
  obtain ⟨δ,sgn,live,pole⟩ := accepted
  exact ⟨δ,scalarEntries w M,sgn,components_at e,live,pole⟩

theorem scalar_point_guard {w M c a} (e : Consequences w M c a) :
    (a.n 1-1) • paperGenerator sqrt2_sq ≠ 0 := by
  rw [←scalar_index,e.scalar_point]
  intro eq
  exact e.step_point_nonzero (scalarEquiv.injective (eq.trans (map_zero scalarEquiv).symm))

#print axioms conjugation_nontrivial
#print axioms multiple_ratio
#print axioms ordinaryAt_eq
#print axioms ordinaryAccepted_iff
#print axioms rootProduct_eq
#print axioms components_at
#print axioms tree_of_points
#print axioms scalar_point_guard
end
end Sun28.Forward
