import ReducedProjection
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Sun28.ConeSieve
open Finset
noncomputable section
open scoped Classical

/-- Independent inclusion of the flags in P, with individual probabilities g(p). -/
def probability (P : Finset ℕ) (g : ℕ → ℝ) (U : Finset ℕ) : ℝ :=
  (∏ p ∈ U, g p) * ∏ p ∈ P \ U, (1 - g p)

def odds (g : ℕ → ℝ) (p : ℕ) := g p / (1-g p)
def indicator (h : Prop) : ℝ := if h then 1 else 0

theorem factor_average (P : Finset ℕ) (g : ℕ → ℝ) (a b : ℕ → ℝ) :
    (∑ U ∈ P.powerset, probability P g U *
       ∏ p ∈ P, (if p∈U then a p else b p)) =
    ∏ p ∈ P, (g p * a p + (1-g p) * b p) := by
  classical
  rw [prod_add]
  apply sum_congr rfl
  intro U hU
  have sub:=mem_powerset.mp hU
  have cut : (P.filter (fun p => p∈U))=U := by ext p; simp; exact fun h=>sub h
  have rest : (P.filter (fun p => p∉U))=P\U := by ext p; simp
  rw [prod_ite,cut,rest,prod_mul_distrib,prod_mul_distrib]
  unfold probability
  ring

theorem model_flag (P r : Finset ℕ) (g : ℕ → ℝ) (sub : r⊆P) :
    (∑ U ∈ P.powerset, probability P g U * indicator (r⊆U)) = ∏ p ∈ r, g p := by
  classical
  let b := fun p : ℕ => if p∈r then (0:ℝ) else 1
  have flag (U : Finset ℕ) : indicator (r⊆U) = ∏ p ∈ P, (if p∈U then (1:ℝ) else b p) := by
    by_cases hr : r⊆U
    · rw [indicator,ite_eq_left hr]
      symm; apply prod_eq_one; intro p hp
      by_cases h : p ∈ U
      · simp [h]
      · simp [h,b,show p∉r from fun e => h (hr e)]
    · obtain ⟨p,pr,pu⟩:=not_subset.mp hr
      rw [indicator,ite_eq_right hr]
      symm; apply prod_eq_zero (sub pr)
      simp [pu,b,pr]
  simp_rw [flag]
  rw [factor_average]
  calc
    _ = ∏ p ∈ P, (if p∈r then g p else 1) := by
      apply prod_congr rfl
      intro p _
      by_cases h : p∈r <;> simp [b,h]
    _ = _ := by
      rw [prod_ite,prod_const_one,mul_one]
      congr 1; ext p; simp; exact fun h=>sub h

/-- One centered factor for each selected sieve prime. -/
def basis (g : ℕ → ℝ) (r U : Finset ℕ) : ℝ :=
  ∏ p ∈ r, (if p∈U then (-1:ℝ) else odds g p)

def coefficient (g : ℕ → ℝ) (r b : Finset ℕ) : ℝ :=
  (∏ p ∈ b, (-1-odds g p)) * ∏ p ∈ r \ b, odds g p

theorem basis_expansion (g : ℕ → ℝ) (r U : Finset ℕ) :
    basis g r U = ∑ b ∈ r.powerset, coefficient g r b * indicator (b⊆U) := by
  classical
  have h (p : ℕ) : (if p∈U then (-1:ℝ) else odds g p) =
      (if p∈U then -1-odds g p else 0) + odds g p := by split_ifs <;> ring
  unfold basis
  simp_rw [h]
  rw [prod_add]
  apply sum_congr rfl
  intro b _
  by_cases hb : b⊆U
  · simp [coefficient,indicator,hb,prod_congr rfl (fun p hp => ite_eq_left (hb hp))]
  · obtain ⟨p,pr,pu⟩:=not_subset.mp hb
    have zero : (∏ p ∈ b, if p∈U then -1-odds g p else 0)=0 := prod_eq_zero pr (by simp [pu])
    simp [indicator,hb,zero]

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.factor_average
#print axioms Sun28.ConeSieve.model_flag
#print axioms Sun28.ConeSieve.basis_expansion
