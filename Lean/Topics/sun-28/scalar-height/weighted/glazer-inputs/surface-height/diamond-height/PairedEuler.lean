import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-! A single product pays for the scalar character and the modular index. -/
namespace ZInQBlueprint.DiamondHeight
noncomputable section

def unitOrders (R : ℕ) : ℕ := ∏ p ∈ R.primeFactors, (p-1)

def eulerFactor (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1+1/(p:ℝ))

theorem euler_mono {s t : Finset ℕ} (st : s ⊆ t) : eulerFactor s ≤ eulerFactor t :=
  Finset.prod_le_prod_of_subset_of_one_le₀ st (fun _ _ => by positivity)
    (fun _ _ _ => le_add_of_nonneg_right (by positivity))

/-- The inequality at 2 also holds: its character factor equals 1. -/
theorem paired_prime {p : ℕ} (hp : p.Prime) :
    ((p-1:ℕ):ℝ)*(1+1/(p:ℝ)) ≤ (p:ℝ) := by
  rw [Nat.cast_sub hp.one_lt.le]
  have pos : (0:ℝ)<p := by exact_mod_cast hp.pos
  field_simp
  norm_num only [Nat.cast_one]
  nlinarith

/-- The ramification radical need not be squarefree. -/
theorem paired_euler {R N : ℕ} (rp : 0<R) (support : N.primeFactors ⊆ R.primeFactors) :
    (unitOrders R:ℝ)*eulerFactor N.primeFactors ≤ R := by
  calc
    _ ≤ (unitOrders R:ℝ)*eulerFactor R.primeFactors :=
      mul_le_mul_of_nonneg_left (euler_mono support) (by positivity)
    _ = ∏ p ∈ R.primeFactors, ((p-1:ℕ):ℝ)*(1+1/(p:ℝ)) := by
      simp only [unitOrders,Nat.cast_prod,eulerFactor,Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ R.primeFactors, (p:ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun _ hp => paired_prime (Nat.prime_of_mem_primeFactors hp))
    _ ≤ R := by rw [← Nat.cast_prod]; exact_mod_cast Nat.le_of_dvd rp (Nat.prod_primeFactors_dvd R)

theorem unitOrders_le {R : ℕ} (rp : 0<R) : unitOrders R≤R := by
  calc
    _ ≤ ∏ p ∈ R.primeFactors,p := Finset.prod_le_prod (fun _ _ => Nat.sub_le ..)
    _ ≤ R := Nat.le_of_dvd rp (Nat.prod_primeFactors_dvd R)

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.euler_mono
#print axioms ZInQBlueprint.DiamondHeight.paired_prime
#print axioms ZInQBlueprint.DiamondHeight.paired_euler
#print axioms ZInQBlueprint.DiamondHeight.unitOrders_le
