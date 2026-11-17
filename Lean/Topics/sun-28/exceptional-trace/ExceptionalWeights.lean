import PoleParameters
import ZInQKernel.Multiplication.Completeness.PoleLocal

/-! Precision of the inverse weight on the identity neighbourhood. -/
namespace Sun28.Exceptional
open Sun28.Ordinary Sun28.ScalarTrace ZInQ.Mult

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))

theorem leaf_precision {R h D : K} {e α ν : ℤ} (k : ℕ)
    (rorder : v R=((e*(ν-6*α):ℤ):WithTop ℤ)) (horder : v h=((e*(α-ν):ℤ):WithTop ℤ))
    (integer : Vge v 0 D) :
    Vge v (e*(3*ν+(10*(k:ℤ)-8)*α)) (R*((D/h^(k+1))/R^k)^2) := by
  have a := integer.div_val' (val_pow_coe horder (k+1))
  have b := a.div_val' (val_pow_coe rorder k)
  apply (Vge.of_eq rorder |>.mul (b.pow 2)).mono
  push_cast
  exact le_of_eq (by ring)

theorem orders_bounded (i : OrdinaryTest) : 1≤(orderRequired i:ℤ) ∧ (orderRequired i:ℤ)≤64 := by
  cases i <;> norm_num [orderRequired]

theorem enough_precision {α ν : ℤ} (k : OrdinaryTest) (large : 6+211*|α|≤ν) :
    2≤3*ν+(10*(orderRequired k:ℤ)-8)*α := by
  have range:=orders_bounded k
  have non : 0≤10*(orderRequired k:ℤ)-8 := by omega
  have upper : 10*(orderRequired k:ℤ)-8≤632 := by omega
  have lower:=mul_le_mul_of_nonneg_left (neg_abs_le α) non
  have bound:=mul_le_mul_of_nonneg_right upper (abs_nonneg α)
  nlinarith only [large,lower,bound,abs_nonneg α]

def normalizedLeaves (h : K) (D : OrdinaryTest → K) (i : OrdinaryTest) : K :=
  D i/h^(orderRequired i+1)

theorem inverse_weight_congruent {R h : K} {e α ν : ℤ} (D : OrdinaryTest → K) (ep : 0<e)
    (rorder : v R=((e*(ν-6*α):ℤ):WithTop ℤ)) (horder : v h=((e*(α-ν):ℤ):WithTop ℤ))
    (integer : ∀ i,Vge v 0 (D i)) (large : 6+211*|α|≤ν) :
    Vge v (2*e) ((weightProduct R (normalizedLeaves h D) orderRequired)⁻¹-1) := by
  apply vge_inv_prod_sub_one Finset.univ (by omega)
  intro i _
  exact (leaf_precision v (orderRequired i) rorder horder (integer i)).mono
    (by simpa only [mul_comm (2:ℤ) e] using mul_le_mul_of_nonneg_left (enough_precision i large) ep.le)

theorem inverse_ne_zero {R h : K} {D : OrdinaryTest → K} {e : ℤ} (ep : 0<e)
    (close : Vge v (2*e) ((weightProduct R (normalizedLeaves h D) orderRequired)⁻¹-1)) :
    weightProduct R (normalizedLeaves h D) orderRequired≠0 := by
  have u:=val_one_add (close.mono (by omega : 1≤2*e))
  rw [add_sub_cancel] at u
  intro z
  simp [z] at u

#print axioms leaf_precision
#print axioms enough_precision
#print axioms inverse_weight_congruent
#print axioms inverse_ne_zero
end Sun28.Exceptional
