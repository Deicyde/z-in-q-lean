import OrdinaryFactors

namespace Sun28.ArtinCube
open Finset
noncomputable section
open scoped Classical
variable {α Ω : Type*} [DecidableEq α]

/-- A weighted, uncentred correlation over an arbitrary finite set of samples.
The weights may already contain the normalising denominator. -/
def moment (X : Finset Ω) (weight : Ω → ℝ) (f : α → Ω → ℝ) (I : Finset α) : ℝ :=
  ∑ x ∈ X, weight x * ∏ i ∈ I,f i x

/-- The exact signed expansion, valid also on wrap cells and for nonuniform sample weights. -/
theorem centered_expand (X : Finset Ω) (weight : Ω → ℝ) (f : α → Ω → ℝ)
    (V : Finset α) (μ : ℝ) :
    moment X weight (fun i x => f i x - μ) V =
      ∑ I ∈ V.powerset, (-μ)^(V \ I).card * moment X weight f I := by
  classical
  unfold moment
  calc
    _ = ∑ x ∈ X, ∑ I ∈ V.powerset, (-μ)^(V \ I).card * (weight x * ∏ i ∈ I,f i x) := by
      apply sum_congr rfl; intro x _
      simp only [sub_eq_add_neg,Finset.prod_add,prod_const,mul_sum]
      apply sum_congr rfl; intro I _; ring
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

/-- Exact cancellation of the conditional Artin main terms on every nonempty set of vertices. -/
theorem main_cancel (V : Finset α) (hv : V.Nonempty) (μ : ℝ) :
    (∑ I ∈ V.powerset, (-μ)^(V \ I).card * μ^I.card) = 0 := by
  classical
  have e := Finset.prod_add (fun _ : α => μ) (fun _ : α => -μ) V
  simpa [mul_comm,Finset.prod_const,hv.ne_empty] using e.symm

/-- Every uncentred moment may have an error ε. Its contribution after centring
is bounded by (1+|μ|)^|V| ε by the finite binomial expansion. -/
theorem centered_bound (X : Finset Ω) (weight : Ω → ℝ) (f : α → Ω → ℝ)
    (V : Finset α) (hv : V.Nonempty) (μ ε : ℝ)
    (H : ∀ I ∈ V.powerset, |moment X weight f I - μ^I.card| ≤ ε) :
    |moment X weight (fun i x => f i x - μ) V| ≤ (1+|μ|)^V.card * ε := by
  classical
  rw [centered_expand]
  have cancel := main_cancel V hv μ
  have e : (∑ I ∈ V.powerset, (-μ)^(V \ I).card * moment X weight f I) =
      ∑ I ∈ V.powerset, (-μ)^(V \ I).card * (moment X weight f I - μ^I.card) := by
    simp only [mul_sub,sum_sub_distrib,cancel,sub_zero]
  have bin := (Finset.prod_add (fun _ : α => (1:ℝ)) (fun _ : α => |μ|) V).symm
  rw [e]
  calc
    _ ≤ ∑ I ∈ V.powerset, |(-μ)^(V \ I).card * (moment X weight f I - μ^I.card)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ I ∈ V.powerset, |μ|^(V \ I).card * ε := by
      apply sum_le_sum; intro I hi;rw [abs_mul,abs_pow,abs_neg]
      exact mul_le_mul_of_nonneg_left (H I hi) (by positivity)
    _ = _ := by rw [←sum_mul]; congr 1;simpa using bin

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.centered_expand
#print axioms Sun28.ArtinCube.main_cancel
#print axioms Sun28.ArtinCube.centered_bound
