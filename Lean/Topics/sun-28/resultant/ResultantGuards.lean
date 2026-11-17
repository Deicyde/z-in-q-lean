import ResultantImage
import GuardResolvent

/-! Literal parameter-ring polynomials implement the locator and every resolvent sample. -/
open Polynomial Finset
namespace ZInQBlueprint.SunResultant.ParamTower
open ZInQBlueprint.SunTower
noncomputable section
variable {R L : Type*} [CommRing R] [Field L] [IsAlgClosed L] [DecidableEq L]

/-- Linear form in the actual tuple variables, over the original parameter ring. -/
def linearForm (R : Type*) [CommRing R] (n b : ℕ) : MvPolynomial (Fin n) R :=
  ∑ i : Fin n, MvPolynomial.X i * (b : MvPolynomial (Fin n) R)^(i : ℕ)

/-- The j-th guard sample is a univariate image polynomial over R. -/
def sample {n : ℕ} (T : ParamTower R n) (b j : ℕ) (f : MvPolynomial (Fin n) R) : R[X] :=
  imagePolynomial T (linearForm R n b + (j : MvPolynomial (Fin n) R)*f)

/-- Every specialization of the literal j-th polynomial agrees with the geometric resolvent
evaluated at U=j, including the recursive multiplicities at collisions. -/
theorem sample_eq_resolvent {n : ℕ} (T : ParamTower R n) (φ : R →+* L)
    (f : MvPolynomial (Fin n) R) (b j : ℕ) (z : L) :
    ((sample T b j f).map φ).eval z =
      (resolvent (rootTuples φ T).toFinset (separator (b:L)) (fun x => MvPolynomial.eval₂Hom φ x f)
         (fun x => (rootTuples φ T).count x) z).eval (j:L) := by
  rw [sample,imagePolynomial_eval_product,Finset.prod_multiset_map_count]
  simp only [SunTower.resolvent,eval_prod,eval_pow,eval_sub,eval_C,eval_mul,eval_X]
  apply Finset.prod_congr rfl
  intro x hx
  congr 1
  simp [linearForm,separator]
  ring

/-- At a separated tuple, f=0 iff every member of the fixed finite family of genuine image
polynomials vanishes at the tuple's projected value. Negation supplies the inequation test. -/
theorem finite_guard_samples [CharZero L] {n : ℕ} (T : ParamTower R n) (φ : R →+* L)
    (f : MvPolynomial (Fin n) R) {b : ℕ}
    (hi : Set.InjOn (separator (b:L)) ((rootTuples φ T).toFinset : Set (Fin n → L)))
    (x : Fin n → L) (hx : Satisfies φ T x) :
    (∀ j : ℕ, j ≤ T.degreeProduct → ((sample T b j f).map φ).IsRoot (separator (b:L) x)) ↔
      MvPolynomial.eval₂Hom φ x f = 0 := by
  let M := rootTuples φ T
  have hx' : x ∈ M.toFinset := Multiset.mem_toFinset.mpr ((mem_rootTuples φ T x).mpr hx)
  have hm (y) (hy : y ∈ M.toFinset) : 0 < M.count y := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hy)
  have hd : (∑ y ∈ M.toFinset, M.count y) ≤ T.degreeProduct := by
    rw [Multiset.toFinset_sum_count_eq]
    exact (card_rootTuples φ T).le
  simp only [IsRoot.def,sample_eq_resolvent]
  exact (resolvent_samples_iff M.toFinset (separator (b:L)) _ (fun y => M.count y) _ hd).trans
    (resolvent_at_separated _ _ _ _ hm hi hx')

end
end ZInQBlueprint.SunResultant.ParamTower
#print axioms ZInQBlueprint.SunResultant.ParamTower.sample_eq_resolvent
#print axioms ZInQBlueprint.SunResultant.ParamTower.finite_guard_samples
