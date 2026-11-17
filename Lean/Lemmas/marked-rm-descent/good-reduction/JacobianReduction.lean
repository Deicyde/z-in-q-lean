import AbelianModel
import ChartSplitting

/-! Application of DDMM 10.3(5) at an even contact or a pole. -/

open CategoryTheory Polynomial IsDiscreteValuationRing
open ZInQBlueprint.ResidueExtension ZInQBlueprint.PrimitiveParameters ZInQBlueprint.DirectCharts
open ZInQBlueprint.PrincipalClusters ZInQBlueprint.RationalReduction ZInQBlueprint.RationalClusters
open ZInQBlueprint.LeadingOrders ZInQBlueprint.ClusterRoots ZInQBlueprint.AbelianModel

namespace ZInQBlueprint.GoodReductionCharts

noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "L" => LocalField p
local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]

/-- The forward implication of DDMM, Theorem 10.3(5), specialized to these
charts. The group scheme provided by `jac` must be the Jacobian of the
smooth completion of y²=f(x). It is a parameter until that construction
and the geometric reading of the cluster tree have been formalized. -/
def DDMMCriterion (jac : Qp[X] → GroupScheme Qp) : Prop :=
  ∀ (u : ℚ) (v a : Zpˣ) (t : Zp) (m : ℕ),
    17 ≤ p → 0 < m →
    ∀ T : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^m),
      let f := polynomial p u v a t
      f.natDegree = 6 → f.Separable →
      (f.Splits ∨ f.IsSplittingField Qp L) →
      (Module.Finite Zp W ∧ Algebra.Etale Zp W) → IsIntegralClosure W Zp L →
      (∀ s ∈ tree, s ≠ Finset.univ → Odd s.card) →
      (∀ s (hs : principal s), Even (principalOrder (equation p u v a t) T s hs)) →
      HasGoodReduction p (jac f)

/-- Good reduction of a single global group scheme follows on both singular
charts. The stated identification must match the local Jacobian of the
full twisted chart with the scalar extension of this very group scheme. -/
theorem goodReductionAt_of_even_contact_or_pole
    (u : ℚ) (hp : 17 ≤ p) (A : GroupScheme ℚ) (jac : Qp[X] → GroupScheme Qp)
    (ddmm : DDMMCriterion p jac)
    (identified : ∀ (v a : Zpˣ) (t : Zp), Coordinates p u t (v : Zp) (a : Zp) →
      Nonempty (jac (polynomial p u v a t) ≅ (baseChange (algebraMap ℚ Qp)).obj A))
    (branch : (∃ k : ℕ, 0 < k ∧ addVal Zp (F p u) = ((2*k : ℕ) : ℕ∞)) ∨
      ∃ g : ℕ, 0 < g ∧ addVal Zp (G p u) = (g : ℕ∞)) : GoodReductionAt p A := by
  have apply_chart (v a : Zpˣ) (t : Zp) {m l : ℕ} (hm : 0 < m)
      (coordinates : Coordinates p u t (v : Zp) (a : Zp))
      (T : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^m))
      (hc : conditions (equation p u v a t) T l) : GoodReductionAt p A := by
    obtain ⟨degree, sep, split⟩ := chart_splitting p u v a t T hc
    obtain ⟨e⟩ := identified v a t coordinates
    exact hasGoodReduction_of_iso p e (ddmm u v a t m hp hm T degree sep split
      (finite_etale p) (integral_closure p) hc.2.1 hc.2.2)
  rcases branch with ⟨k, hk, hF⟩ | ⟨g, hg, hG⟩
  · obtain ⟨t, v, a, coordinates, T, hc⟩ := even_contact_chart p u hp k hk hF
    exact apply_chart v a t hk coordinates T hc
  · obtain ⟨t, a, coordinates, T, hc, _⟩ := pole_chart p u hp g hg hG
    exact apply_chart 1 a t hg coordinates T hc

end
end ZInQBlueprint.GoodReductionCharts

#print axioms ZInQBlueprint.GoodReductionCharts.DDMMCriterion
#print axioms ZInQBlueprint.GoodReductionCharts.goodReductionAt_of_even_contact_or_pole
