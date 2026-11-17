import ConeMoments

namespace Sun28.ConeSieve
open Finset
noncomputable section
open scoped Classical

/-- The contribution of a finite weighted set to a real test function of its flags. -/
def mass {α : Type*} (S : Finset α) (w : α → ℝ) (flags : α → Finset ℕ)
    (f : Finset ℕ → ℝ) := ∑ x ∈ S, w x * f (flags x)

def intersections {α : Type*} (S : Finset α) (w : α → ℝ)
    (flags : α → Finset ℕ) (r : Finset ℕ) := mass S w flags (fun U => indicator (r⊆U))

theorem intersection_expansion {α : Type*} (S : Finset α) (w : α → ℝ) (flags : α → Finset ℕ)
    (g : ℕ → ℝ) (r s : Finset ℕ) :
    mass S w flags (fun U => basis g r U * basis g s U) =
    ∑ b ∈ r.powerset, ∑ c ∈ s.powerset,
      (coefficient g r b * coefficient g s c) * intersections S w flags (b∪c) := by
  classical
  unfold intersections mass
  simp_rw [basis_expansion]
  simp only [sum_mul,mul_sum]
  rw [sum_comm,Finset.sum_comm (s:=r.powerset) (t:=s.powerset)]
  apply sum_congr rfl; intro c _
  rw [sum_comm]
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro x _
  by_cases h : b⊆flags x <;> by_cases k : c⊆flags x <;> simp [indicator,union_subset_iff,h,k];ring

/-- Local comparison of one Gram-matrix entry with its exact independent model. -/
theorem gram_error {α : Type*} (S : Finset α) (w : α → ℝ) (flags : α → Finset ℕ)
    (P : Finset ℕ) (g : ℕ → ℝ) (X E : ℝ) (r s : Finset ℕ) (hr : r⊆P) (hs : s⊆P)
    (lt : ∀ p∈P,g p<1)
    (remainder : ∀ b⊆r, ∀ c⊆s,
      |intersections S w flags (b∪c) - X * ∏ p ∈ b∪c, g p| ≤ E) :
    |mass S w flags (fun U => basis g r U * basis g s U) -
        X*(if r=s then ∏ p ∈ r, odds g p else 0)| ≤
    ((∑ b∈r.powerset, |coefficient g r b|)*(∑ c∈s.powerset, |coefficient g s c|))*E := by
  classical
  let model := P.powerset
  let v := probability P g
  have modelMass (b c : Finset ℕ) (hb : b⊆r) (hc : c⊆s) :
      intersections model v id (b∪c)=∏ p ∈ b∪c,g p :=
    model_flag P (b∪c) g (union_subset (hb.trans hr) (hc.trans hs))
  have orth : mass model v id (fun U=>basis g r U*basis g s U) =
      if r=s then ∏ p∈r,odds g p else 0 := orthogonal P r s g hr hs lt
  rw [←orth,intersection_expansion,intersection_expansion]
  simp only [mul_sum,←sum_sub_distrib]
  calc
    _ ≤ ∑ b∈r.powerset, |∑ c∈s.powerset,
        ((coefficient g r b*coefficient g s c)*intersections S w flags (b∪c) -
          X*((coefficient g r b*coefficient g s c)*intersections model v id (b∪c)))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ b∈r.powerset, ∑ c∈s.powerset, |coefficient g r b| * |coefficient g s c| * E := by
      apply sum_le_sum; intro b hb
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum; intro c hc
      have rr:=remainder b (mem_powerset.mp hb) c (mem_powerset.mp hc)
      rw [modelMass b c (mem_powerset.mp hb) (mem_powerset.mp hc)]
      rw [show ∀ e a u v : ℝ,e*a-u*(e*v)=e*(a-u*v) from fun _ _ _ _=>by ring,
        abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left rr (by positivity)
    _ = (∑ c∈s.powerset,(∑ b∈r.powerset,|coefficient g r b|)*|coefficient g s c|)*E := by
      simp only [sum_mul];rw [sum_comm]

theorem coefficient_sum (g : ℕ → ℝ) (r : Finset ℕ) (non : ∀ p∈r,0≤odds g p) :
    (∑ b∈r.powerset, |coefficient g r b|) = ∏ p∈r,(1+2*odds g p) := by
  classical
  calc
    _ = ∑ b∈r.powerset, (∏ p∈b,(1+odds g p)) * ∏ p∈r\b,odds g p := by
      apply sum_congr rfl; intro b hb
      have sub:=mem_powerset.mp hb
      have a : (∏ p∈b, |(-1:ℝ)-odds g p|)=∏ p∈b,(1+odds g p) := by
        apply prod_congr rfl; intro p hp
        rw [abs_of_nonpos (by linarith [non p (sub hp)])];ring
      rw [coefficient,abs_mul,abs_prod,a,abs_of_nonneg (prod_nonneg (fun p hp => non p (mem_sdiff.mp hp).1))]
    _ = _ := by
      rw [←prod_add]; apply prod_congr rfl; intro p _;ring

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.intersection_expansion
#print axioms Sun28.ConeSieve.gram_error
#print axioms Sun28.ConeSieve.coefficient_sum
