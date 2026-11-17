import NormalizedFibre
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.LocalSubring

/-! A two-centre bound for all the weights of the integral sextic, without residue or ramification restrictions. -/
open Polynomial
namespace ZInQBlueprint.NonarchContact
open DirectCharts IntegralSextic BranchDepth
noncomputable section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

private theorem sub_max (x y : K) : ‖x-y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg,norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

private theorem nat_small (n : ℕ) : ‖(n:K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

/-- All roots of a monic integral chart have norm at most one. -/
theorem root_integral {t x : K} (ht : ‖t‖ ≤ 1) (hx : form 1 t x 1=0) : ‖x‖ ≤ 1 := by
  let V := (NormedField.valuation (K:=K)).valuationSubring
  let z : V := ⟨t,ht⟩
  have he : IsIntegral V x := by
    refine ⟨monicSextic z,(monic_six z).1,?_⟩
    simpa [monicSextic,form,alpha,beta,gamma,z] using hx
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral he
  exact hy ▸ y.2

/-- The equation controls the norm of the product of the two distances. -/
theorem alpha_sq {t x : K} (ht : ‖t‖ ≤ 1) (hx : form 1 t x 1=0) :
    ‖(x*(x+3))‖^2 ≤ ‖t‖ := by
  have hx₁ := root_integral ht hx
  let a := x*(x+3)
  let b := x+2
  let c := x^2+4*x+6
  have ha : ‖a‖ ≤ 1 := by
    rw [show a=x*(x+3) from rfl,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hx₁ (nat_small 3)))).trans hx₁
  have hb : ‖b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx₁ (nat_small 2))
  have hc : ‖c‖ ≤ 1 := by
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    refine max_le ?_ (nat_small 6)
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [norm_pow,norm_mul]
    exact max_le (pow_le_one₀ (norm_nonneg _) hx₁) ((mul_le_of_le_one_right (norm_nonneg _) hx₁).trans (nat_small 4))
  have he : a^3=t*a*b*c-t^2*b^3 := by
    simp [form,alpha,beta,gamma] at hx
    dsimp [a,b,c]
    linear_combination hx
  have hle : ‖a‖^3 ≤ max (‖t‖*‖a‖) (‖t‖^2) := by
    rw [←norm_pow,he]
    refine (sub_max _ _).trans (max_le_max ?_ ?_)
    · simp only [norm_mul]
      calc _ ≤ ‖t‖*‖a‖*‖b‖ := mul_le_of_le_one_right (by positivity) hc
           _ ≤ _ := mul_le_of_le_one_right (by positivity) hb
    · simp only [norm_mul,norm_pow]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hb)
  change ‖a‖^2 ≤ ‖t‖
  by_contra! hbad
  have hap : 0 < ‖a‖ := by nlinarith [norm_nonneg a,norm_nonneg t]
  have hat : ‖t‖ < ‖a‖ := hbad.trans_le (by nlinarith [mul_nonneg (norm_nonneg a) (sub_nonneg.mpr ha)])
  rw [max_eq_left (by simpa only [pow_two] using (mul_le_mul_of_nonneg_left hat.le (norm_nonneg t)))] at hle
  nlinarith [mul_lt_mul_of_pos_right hbad hap]

variable [CharZero K]

/-- At least one of the two centres is within sqrt(‖t‖)/‖3‖ of each root. -/
theorem close_to_centre {t x : K} (ht : ‖t‖ ≤ 1) (hx : form 1 t x 1=0) :
    ‖x‖ ≤ Real.sqrt ‖t‖ / ‖(3:K)‖ ∨ ‖x+3‖ ≤ Real.sqrt ‖t‖ / ‖(3:K)‖ := by
  have hp : 0 < ‖(3:K)‖ := norm_pos_iff.mpr (by norm_num)
  have hd : ‖(3:K)‖ ≤ max ‖x+3‖ ‖x‖ := by simpa using sub_max (x+3) x
  have ha := alpha_sq ht hx
  have h : ‖x‖*‖x+3‖ ≤ Real.sqrt ‖t‖ := by
    rw [norm_mul] at ha
    exact (Real.le_sqrt (by positivity) (norm_nonneg _)).mpr ha
  rcases le_max_iff.mp hd with hbig|hbig
  · left
    exact (le_div_iff₀ hp).mpr ((mul_le_mul_of_nonneg_left hbig (norm_nonneg _)).trans h)
  · right
    exact (le_div_iff₀ hp).mpr ((mul_le_mul_of_nonneg_left hbig (norm_nonneg _)).trans (by simpa only [mul_comm] using h))

omit [CharZero K] in
private theorem triangle_bound {r : Fin 6 → K} {B : ℝ}
    (h1 : ∀ i, ‖r i‖ ≤ 1) (h : ∀ i, ‖r i‖ ≤ B ∨ ‖r i+3‖ ≤ B)
    (i j k : Fin 6) : ‖triangle r i j k‖ ≤ B := by
  have diff (a b : Fin 6) : ‖r a-r b‖ ≤ 1 := (sub_max _ _).trans (max_le (h1 _) (h1 _))
  have near (a b : Fin 6) (ha : ‖r a‖ ≤ B) (hb : ‖r b‖ ≤ B) : ‖r a-r b‖ ≤ B :=
    (sub_max _ _).trans (max_le ha hb)
  have far (a b : Fin 6) (ha : ‖r a+3‖ ≤ B) (hb : ‖r b+3‖ ≤ B) : ‖r a-r b‖ ≤ B := by
    simpa only [add_sub_add_right_eq_sub] using (sub_max (r a+3) (r b+3)).trans (max_le ha hb)
  have pigeon : ‖r i-r j‖ ≤ B ∨ ‖r i-r k‖ ≤ B ∨ ‖r j-r k‖ ≤ B := by
    rcases h i with hi|hi <;> rcases h j with hj|hj <;> rcases h k with hk|hk <;>
      first | exact Or.inl (near _ _ hi hj) | exact Or.inl (far _ _ hi hj)
            | exact Or.inr (Or.inl (near _ _ hi hk)) | exact Or.inr (Or.inl (far _ _ hi hk))
            | exact Or.inr (Or.inr (near _ _ hj hk)) | exact Or.inr (Or.inr (far _ _ hj hk))
  simp only [triangle,norm_mul]
  rcases pigeon with h'|h'|h'
  · exact (mul_le_of_le_one_right (by positivity) (diff j k)).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (diff i k)).trans h')
  · exact (mul_le_of_le_one_right (by positivity) (diff j k)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (diff i j)).trans h')
  · exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_right (norm_nonneg _) (diff i k)).trans (diff i j))).trans h'

/-- This estimate holds at every residue characteristic and for all contact orders. -/
theorem weight_bound {t : K} (ht : ‖t‖ ≤ 1) (r : Fin 6 → K)
    (hz : ∀ i, form 1 t (r i) 1=0) (i : Fin 10) :
    ‖weight r i‖ * ‖(3:K)‖^4 ≤ ‖t‖^2 := by
  let B := Real.sqrt ‖t‖ / ‖(3:K)‖
  have h (i j k : Fin 6) : ‖triangle r i j k‖ ≤ B :=
    triangle_bound (fun l => root_integral ht (hz l)) (fun l => close_to_centre ht (hz l)) i j k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh : ‖weight r i‖ ≤ (B*B)^2 := by
    rw [weight,norm_pow,norm_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (h ..) (h ..) (norm_nonneg _) hB) 2
  calc ‖weight r i‖ * ‖(3:K)‖^4 ≤ (B*B)^2*‖(3:K)‖^4 := mul_le_mul_of_nonneg_right hh (by positivity)
       _ = ‖t‖^2 := by
         have h3 : ‖(3:K)‖ ≠ 0 := norm_ne_zero_iff.mpr (by norm_num)
         dsimp [B]
         field_simp [h3]
         nlinarith [Real.sq_sqrt (norm_nonneg t),sq_nonneg (Real.sqrt ‖t‖),
           congrArg (fun x:ℝ => x^2) (Real.sq_sqrt (norm_nonneg t))]

end
end ZInQBlueprint.NonarchContact
#print axioms ZInQBlueprint.NonarchContact.root_integral
#print axioms ZInQBlueprint.NonarchContact.alpha_sq
#print axioms ZInQBlueprint.NonarchContact.close_to_centre
#print axioms ZInQBlueprint.NonarchContact.weight_bound
