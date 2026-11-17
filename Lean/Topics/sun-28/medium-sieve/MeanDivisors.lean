import ActualTail
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Sun28.MediumSieve
open Finset
open scoped Classical
noncomputable section

/-- Every divisor of a product is a product of two divisors, without a coprimality condition. -/
theorem divisor_submult (a b : ℕ) :
    (a*b).divisors.card ≤ a.divisors.card*b.divisors.card := by
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  have sub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun z=>z.1*z.2) := by
    intro m hm
    obtain ⟨u,v,hu,hv,eq⟩:=exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hm)
    exact mem_image.mpr ⟨(u,v),mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hu,ha⟩,Nat.mem_divisors.mpr ⟨hv,hb⟩⟩,eq.symm⟩
  simpa using (card_le_card sub).trans card_image_le

/-- If e² b divides v² with b squarefree, then eb divides v. -/
theorem squarefree_kernel {e b v : ℕ} (hp : e≠0) (sq : Squarefree b) (dv : e^2*b∣v^2) :
    e*b ∣ v := by
  have es : e^2 ∣ v^2 := dvd_trans (dvd_mul_right (e^2) b) dv
  obtain ⟨q,rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp es
  rw [mul_pow] at dv
  have bd : b∣q^2 := (Nat.mul_dvd_mul_iff_left (pow_pos (Nat.pos_of_ne_zero hp) 2)).mp dv
  exact mul_dvd_mul_left e ((sq.dvd_pow_iff_dvd (by decide : 2≠0)).mp bd)

def cells (W v : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 W) ×ˢ (Icc 1 W)).filter fun z=>z.1*z.2∣v

/-- A divisor e² b of v² is recoverable from one of the pairs (e,b) with eb dividing v. -/
theorem square_divisors {v W : ℕ} (pos : 0<v) (bound : v≤W) :
    (v^2).divisors.card ≤ (cells W v).card := by
  have sub : (v^2).divisors ⊆ (cells W v).image (fun z=>z.1^2*z.2) := by
    intro n hn
    obtain ⟨e,b,eq,sq⟩:=exists_sq_mul_squarefree n
    have np:=Nat.pos_of_mem_divisors hn
    have ep : 0<e := by by_contra! h; simp [show e=0 by omega] at eq;omega
    have bp : 0<b := Nat.pos_of_ne_zero sq.ne_zero
    have dv:=Nat.dvd_of_mem_divisors hn
    rw [←eq] at dv
    have product:=squarefree_kernel ep.ne' sq dv
    have lim: e*b≤W := (Nat.le_of_dvd pos product).trans bound
    have eBound : e≤W := (Nat.le_mul_of_pos_right e bp).trans lim
    have bBound : b≤W := (Nat.le_mul_of_pos_left b ep).trans lim
    exact mem_image.mpr ⟨(e,b),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ep,eBound⟩,mem_Icc.mpr ⟨bp,bBound⟩⟩,product⟩,eq⟩
  exact (card_le_card sub).trans card_image_le

end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.divisor_submult
#print axioms Sun28.MediumSieve.squarefree_kernel
#print axioms Sun28.MediumSieve.square_divisors
