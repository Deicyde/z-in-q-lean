import RationalJacobian
import OrdinaryReduction

/-! The two-triple case of the published cluster criterion, on the
unpointed Picard variety of the actual smooth completion. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial IsDiscreteValuationRing
namespace ZInQBlueprint.LocalJacobians
open BinaryCover AbelianModel ResidueExtension ClusterPicture ClusterRoots PrincipalClusters
open GoodReductionCharts RationalReduction LeadingOrders DirectCharts
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "L" => LocalField p
local notation "Qp" => ℚ_[p]

/-- The Jacobian is the unpointed degree-zero Picard variety, with its group law. -/
def jacobian {K : Type} [Field K] (D : Over (Spec (.of K)))
    [IsProper D.hom] [GeometricallyIntegral D.hom] [SmoothOfRelativeDimension 1 D.hom] :
    GroupScheme K := by
  let f := JacobianVarieties.Picard.Unpointed.toBase K D.hom
  let G := JacobianVarieties.Picard.Unpointed.groupLaw K D.hom
  let : GrpObj (Over.mk f) := G.grpObjOverMk
  let : IsCommMonObj (Over.mk f) := G.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
    (JacobianVarieties.Picard.Unpointed.groupLaw_commutative K D.hom)
  exact ⟨Over.mk f⟩

/-- All the curve hypotheses of the Picard construction hold on each singular
chart over Q_p, although its displayed integral equation has a singular fibre. -/
theorem chart_geometry {u : ℚ} (hu : u ∉ ZInQ.contactSet) (v a : ℤ_[p]ˣ) (t : ℤ_[p])
    (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    let D := sexticCompletion (polynomial p u v a t) (ddmm_sextic_regular hu v a t hc).1
    IsProper D.hom ∧ GeometricallyIntegral D.hom ∧ SmoothOfRelativeDimension 1 D.hom := by
  let D := sexticCompletion (polynomial p u v a t) (ddmm_sextic_regular hu v a t hc).1
  obtain ⟨hI, hP, hSm, hdim, _⟩ := sexticCompletion_geometry
    (ddmm_sextic_regular hu v a t hc).1 (ddmm_sextic_regular hu v a t hc).2
  let : AlgebraicGeometry.IsIntegral D.left := hI
  let : Smooth D.hom := hSm
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  have base : GeometricallyIntegral (paperPullback Qp u).hom := inferInstanceAs
    (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qp)))
  obtain ⟨_, _, e, _, _⟩ := ddmm_smooth_completion_iso hu v a t hc
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  refine ⟨hP, ?_, SixJacobian.relative_dimension_one D.hom hdim⟩
  have sq : IsPullback e.inv.left D.hom (paperPullback Qp u).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.inv.w⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) sq base

/-- DDMM, Theorem 10.3(5), for any sextic having two triples in this unramified
quadratic ring. The roots refer to the given polynomial and the orders use
its own leading coefficient. There is no parameter from the six-contact family. -/
def TwoTripleGoodReduction : Prop :=
  ∀ (f : Qp[X]) (hd : f.natDegree = 6), f.Separable →
    ∀ (g : W[X]) (c : W) (m l : ℕ), 2 < p → 0 < m →
      ∀ T : SexticFibre g ((p : W)^m),
        f.map (algebraMap Qp L) = (C c*g).map (algebraMap W L) →
        g.Monic → addVal W c = (l : ℕ∞) →
        (f.Splits ∨ f.IsSplittingField Qp L) →
        (Module.Finite ℤ_[p] W ∧ Algebra.Etale ℤ_[p] W) → IsIntegralClosure W ℤ_[p] L →
        (∀ s ∈ tree, s ≠ Finset.univ → Odd s.card) →
        (∀ s (hs : principal s), Even (principalOrder (C c*g) T s hs)) →
        let D := sexticCompletion f hd
        ∀ [IsProper D.hom] [GeometricallyIntegral D.hom] [SmoothOfRelativeDimension 1 D.hom],
          HasGoodReduction p (jacobian D)

/-- The geometric hypotheses of the two-triple criterion hold for the signed
sextic at both even contacts and poles. Its conclusion is now about the
Jacobian of a specified Q_p-curve which is isomorphic to the paper fibre. -/
theorem good_chart (criterion : TwoTripleGoodReduction p) {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hp : 17 ≤ p) (v a : ℤ_[p]ˣ) (t : ℤ_[p])
    (coord : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p]))
    {m l : ℕ} (hm : 0 < m)
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^m))
    (h : conditions (equation p u v a t) T l) :
    let D := sexticCompletion (polynomial p u v a t) (ddmm_sextic_regular hu v a t coord).1
    let G := chart_geometry p hu v a t coord
    letI := G.1
    letI := G.2.1
    letI := G.2.2
    HasGoodReduction p (jacobian D) := by
  have ⟨hd, hs, split⟩ := chart_splitting p u v a t T h
  let D := sexticCompletion (polynomial p u v a t) hd
  have G := chart_geometry p hu v a t coord
  let : IsProper D.hom := G.1
  let : GeometricallyIntegral D.hom := G.2.1
  let : SmoothOfRelativeDimension 1 D.hom := G.2.2
  let c := (equation p u v a t).leadingCoeff
  have he : equation p u v a t = C c * monicSextic (fromPadics p t) := by
    dsimp only [c, equation]
    rw [leading, chart]
  apply criterion _ hd hs _ c m l (by omega) hm T
    ((polynomial_map p u v a t).trans (congrArg (Polynomial.map (algebraMap W L)) he))
    (monic_six _).1 h.1 split (finite_etale p) (integral_closure p) h.2.1
  exact fun s hs => by rw [← he]; exact h.2.2 s hs

end
end ZInQBlueprint.LocalJacobians
#print axioms ZInQBlueprint.LocalJacobians.jacobian
#print axioms ZInQBlueprint.LocalJacobians.chart_geometry
#print axioms ZInQBlueprint.LocalJacobians.TwoTripleGoodReduction
#print axioms ZInQBlueprint.LocalJacobians.good_chart
