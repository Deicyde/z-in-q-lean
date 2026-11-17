import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

namespace Sun28.SupportMatrix
open Matrix
abbrev F := ZMod 2
abbrev Vec (ι : Type*) := ι → F
variable {ι : Type*} [Fintype ι]

theorem outer_apply (u v x : Vec ι) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_comm, mul_left_comm]

variable [DecidableEq ι]

/-- Two products with a grounded inverse certify the rank-one correction.
In the application the grounding functional evaluates at the deleted index. -/
structure Certificate (K : Matrix ι ι F) (s l a b e : Vec ι) where
  inverse : Matrix ι ι F
  constants : K *ᵥ 1 = 0
  marked : K *ᵥ b = 0
  odd_sign : (1 : Vec ι) ⬝ᵥ s = 1
  selector_total : a ⬝ᵥ 1 = 0
  selector_mark : a ⬝ᵥ b = 1
  reciprocity : K + Kᵀ = vecMulVec s s + diagonal s
  left_product : inverse * (K + vecMulVec l a) = 1 - vecMulVec 1 e
  right_product : (K + vecMulVec l a) * inverse = 1 - vecMulVec e 1

theorem grounded_kernel {C A : Matrix ι ι F} {e x : Vec ι}
    (h : C * A = 1 - vecMulVec 1 e) (hx : A *ᵥ x = 0) : x = (e ⬝ᵥ x) • 1 := by
  have hz : ((1 : Matrix ι ι F) - vecMulVec 1 e) *ᵥ x = 0 := by
    rw [← h, ← mulVec_mulVec, hx, mulVec_zero]
  rwa [sub_mulVec, one_mulVec, outer_apply, sub_eq_zero] at hz

/-- The sign and 3-adic rows kill the second support vector. -/
theorem second_zero {K : Matrix ι ι F} {s l a b e v : Vec ι}
    (D : Certificate K s l a b e) (hs : (K + diagonal s) *ᵥ v = 0)
    (h3 : (l + s) ⬝ᵥ v = 0) : v = 0 := by
  have hr := congrArg (fun M : Matrix ι ι F => M *ᵥ v) D.reciprocity
  simp only [add_mulVec, outer_apply] at hr hs
  have hT : Kᵀ *ᵥ v = (s ⬝ᵥ v) • s := by
    have hD := eq_neg_of_add_eq_zero_left hs
    rw [hD, ZModModule.neg_eq_self] at hr
    exact add_left_cancel (hr.trans (add_comm _ _))
  have hsign : s ⬝ᵥ v = 0 := by
    have hp := congrArg (fun z : Vec ι => (1 : Vec ι) ⬝ᵥ z) hT
    simpa only [dotProduct_transpose_mulVec, D.constants, dotProduct_zero, dotProduct_smul,
      D.odd_sign, smul_eq_mul, mul_one, eq_comm] using hp
  have hl : l ⬝ᵥ v = 0 := by simpa [add_dotProduct, hsign] using h3
  have hz : (K + vecMulVec l a)ᵀ *ᵥ v = 0 := by
    simp [transpose_add, transpose_vecMulVec, add_mulVec, outer_apply, hT, hsign, hl]
  have hground := congrArg Matrix.transpose D.right_product
  simp only [transpose_mul, transpose_sub, transpose_one, transpose_vecMulVec] at hground
  have hconst := grounded_kernel hground hz
  have hc := congrArg (fun z : Vec ι => s ⬝ᵥ z) hconst
  have hsone : s ⬝ᵥ 1 = 1 := (dotProduct_comm _ _).trans D.odd_sign
  simp only [hsign, dotProduct_smul, hsone, smul_eq_mul, mul_one] at hc
  simpa [← hc] using hconst

/-- The first support vector has only its constant and marked directions. -/
theorem first_span {K : Matrix ι ι F} {s l a b e u : Vec ι} {δ : F}
    (D : Certificate K s l a b e) (hu : K *ᵥ u = δ • l) :
    δ = 0 ∧ ∃ c d : F, u = c • 1 + d • b := by
  let d := a ⬝ᵥ u + δ
  let w := u - d • b
  have haw : a ⬝ᵥ w = -δ := by
    simp [w, d, dotProduct_sub, D.selector_mark, smul_eq_mul]
  have hz : (K + vecMulVec l a) *ᵥ w = 0 := by
    rw [add_mulVec, outer_apply, haw]
    simp [w, mulVec_sub, mulVec_smul, D.marked, hu, ZModModule.add_self]
  have hconst := grounded_kernel D.left_product hz
  have hzero : a ⬝ᵥ w = 0 := by
    calc
      a ⬝ᵥ w = a ⬝ᵥ ((e ⬝ᵥ w) • 1) := congrArg (fun z => a ⬝ᵥ z) hconst
      _ = 0 := by simp [D.selector_total]
  exact ⟨neg_eq_zero.mp (haw.symm.trans hzero), e ⬝ᵥ w, d, sub_eq_iff_eq_add.mp hconst⟩

theorem rows_iff {K : Matrix ι ι F} {s l a b e u v : Vec ι} {δ : F}
    (D : Certificate K s l a b e) :
    (K *ᵥ u + diagonal l *ᵥ v = δ • l ∧
      (K + diagonal s) *ᵥ v = 0 ∧ (l + s) ⬝ᵥ v = 0) ↔
      v = 0 ∧ δ = 0 ∧ ∃ c d : F, u = c • 1 + d • b := by
  constructor
  · rintro ⟨hu, hs, h3⟩
    obtain rfl := second_zero D hs h3
    exact ⟨rfl, first_span D (by simpa using hu)⟩
  · rintro ⟨rfl, rfl, c, d, rfl⟩
    simp [mulVec_add, mulVec_smul, D.constants, D.marked]

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.outer_apply
#print axioms Sun28.SupportMatrix.grounded_kernel
#print axioms Sun28.SupportMatrix.second_zero
#print axioms Sun28.SupportMatrix.first_span
#print axioms Sun28.SupportMatrix.rows_iff
