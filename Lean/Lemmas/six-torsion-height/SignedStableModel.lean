import QuaternionGoodHeight
import SignedQuinticCompletion

/-! A restricted Weierstrass model and good abelian reduction over one field. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField
namespace ZInQBlueprint.TorsionHeight
open BinaryCover WeightedCurvePoints
noncomputable section

/-- The same number field works for every finite place and for a monic
quintic presentation of the literal base-changed curve. The displayed open
immersion identifies the chart containing the chosen branch section. -/
theorem signed_stable_model {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (field : ThetaClass.PrintedField hu) (pqm : QuaternionPotentialReduction)
    (st : SerreTateCriterion (SixJacobian.jacobian hu)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      FullLevel (SixJacobian.jacobian hu) 12 K ∧
      (∀ v : FinitePlace K, GoodAt (SixJacobian.jacobian hu) v) ∧
      Nat.card (fixedSections K u) = 6 ∧
      let f := paper K u false
      ∃ (a : K) (_ : f.IsRoot a) (deg : (reciprocalSextic f a).natDegree = 6),
        (reciprocalSextic f a).reverse = oddPolynomial f a ∧
        (oddPolynomial f a).Monic ∧ (oddPolynomial f a).natDegree = 5 ∧
        (oddPolynomial f a).Splits ∧ (oddPolynomial f a).Separable ∧
        ∃ j : SpecOver (R := K) (Cover (reciprocalSextic f a)) ⟶ paperPullback K u,
          IsOpenImmersion j.left ∧
          ∃! e : sexticCompletion (reciprocalSextic f a) deg ≅ paperPullback K u,
            chartInclusion K _ _ (reverse_sextic_overlap deg) false ≫ e.hom = j := by
  obtain ⟨K,kf,kn,level,good,sp,six,_,_⟩ := signed_height_field_good hu field pqm st
  let := kf
  let := kn
  let f := paper K u false
  have hd := finite_degree K hu
  obtain ⟨a,ha⟩ := sp.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [hd]; decide))
  have hs := odd_roots_split_separable hd sp (paper_chart_regular K hu false).2 (show f.IsRoot a from ha)
  obtain ⟨deg,identity,j,openj,uniq⟩ := signed_quintic_completion hu (show f.IsRoot a from ha)
  obtain ⟨monic,deg5⟩ := oddPolynomial_monic_degree f a
  exact ⟨K,kf,kn,level,good,six,a,ha,deg,identity,monic,deg5,hs.1,hs.2.1,j,openj,uniq⟩

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.signed_stable_model

